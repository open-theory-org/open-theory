#!/usr/bin/env python3
"""Produce a `pool-rate` or `judged-rate` v0.1 certificate (untrusted; specs/claims/).

  commit  hash the pool into a Merkle root, fix n, δ and a future drand round, write
          commitment.json and timestamp it (RFC 3161) before the round exists. With --audit-m the
          pool items carry a committed `judge` label and the claim is `judged-rate`.
  prove   once the round is published: derive the sample, attach inclusion proofs and labels
          (gold labels for the first m items for `judged-rate`), count failures, find the tightest
          bounds the decision procedure accepts, write the bundle.

`ot verify <bundle>` re-checks everything. Nothing here is trusted.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import binomial_bound  # noqa: E402

_spec = importlib.util.spec_from_file_location("ot_merkle", ROOT / "verifier" / "core" / "merkle.py")
merkle = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(merkle)

DOMAIN = b"opentheory/pool-rate/v0.1"
DRAND = "https://api.drand.sh"
DEFAULT_CHAIN = "8990e7a9aaed2ffed73dbd7092123d6f289930540d7651336225dc172e51b2ce"
ASSUMPTIONS = ["A5-beacon", "A6-timestamp", "A7-issuer-identity"]
EXACT_TAIL_MAX_K = 2000  # above this, use a Chernoff witness (one kernel comparison)


def write_json(path: Path, obj) -> str:
    data = json.dumps(obj, separators=(",", ":")).encode()
    path.write_bytes(data)
    return hashlib.sha256(data).hexdigest()


def read_pool(path: Path) -> list:
    with path.open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def derive_indices(round_: int, signature: bytes, n: int, size: int) -> list[int]:
    head = DOMAIN + round_.to_bytes(8, "big") + signature
    return [int.from_bytes(hashlib.sha256(head + i.to_bytes(8, "big")).digest(), "big") % size
            for i in range(n)]


# ---------------------------------------------------------------- drand

def drand_get(chain: str, what: str) -> dict:
    with urllib.request.urlopen(f"{DRAND}/{chain}/{what}", timeout=20) as r:
        return json.load(r)


def fetch_round(chain: str, round_: int, wait: bool = True) -> dict:
    info = drand_get(chain, "info")
    publish = info["genesis_time"] + (round_ - 1) * info["period"]
    while wait and time.time() < publish + 2:
        time.sleep(min(5.0, publish + 2 - time.time()))
    r = drand_get(chain, f"public/{round_}")
    return {"chain": chain, "round": r["round"], "signature": r["signature"],
            "previous_signature": r["previous_signature"]}


# ---------------------------------------------------------------- timestamps

def tsa_local(digest_hex: str, tsa_dir: Path) -> bytes:
    """Stamp with a local test authority made by `make_test_tsa` (for tests and demos only)."""
    with tempfile.TemporaryDirectory() as tmp:
        q = Path(tmp) / "q.tsq"
        out = Path(tmp) / "r.tsr"
        subprocess.run(["openssl", "ts", "-query", "-digest", digest_hex, "-sha256", "-cert", "-out", str(q)],
                       check=True, capture_output=True)
        subprocess.run(["openssl", "ts", "-reply", "-queryfile", str(q), "-config", str(tsa_dir / "tsa.cnf"),
                        "-out", str(out)], check=True, capture_output=True, cwd=tsa_dir)
        return out.read_bytes()


def tsa_url(digest_hex: str, url: str) -> bytes:
    """Stamp with a public RFC 3161 authority (sends only the digest)."""
    with tempfile.TemporaryDirectory() as tmp:
        q = Path(tmp) / "q.tsq"
        subprocess.run(["openssl", "ts", "-query", "-digest", digest_hex, "-sha256", "-cert", "-out", str(q)],
                       check=True, capture_output=True)
        req = urllib.request.Request(url, data=q.read_bytes(),
                                     headers={"Content-Type": "application/timestamp-query"})
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.read()


def make_test_tsa(tsa_dir: Path) -> Path:
    """A throwaway CA and timestamp authority. Its root is trusted only where a verifier is told to."""
    tsa_dir.mkdir(parents=True, exist_ok=True)
    cnf = tsa_dir / "tsa.cnf"
    cnf.write_text("""[ req ]
distinguished_name = dn
prompt = no
[ dn ]
CN = OpenTheory TEST timestamp authority (not trusted)
[ tsa_ext ]
basicConstraints = CA:FALSE
keyUsage = critical, digitalSignature
extendedKeyUsage = critical, timeStamping
[ ca_ext ]
basicConstraints = critical, CA:TRUE
keyUsage = critical, keyCertSign
[ tsa ]
default_tsa = tsa1
[ tsa1 ]
dir = .
serial = ./serial
signer_cert = ./tsa.crt
certs = ./ca.crt
signer_key = ./tsa.key
signer_digest = sha256
default_policy = 1.3.6.1.4.1.99999.1
digests = sha256
accuracy = secs:1
ordering = no
tsa_name = no
ess_cert_id_chain = no
ess_cert_id_alg = sha256
""")
    run = lambda *a: subprocess.run(list(a), check=True, capture_output=True, cwd=tsa_dir)
    run("openssl", "req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:P-256", "-nodes",
        "-keyout", "ca.key", "-out", "ca.crt", "-days", "36500", "-subj", "/CN=OpenTheory TEST root (not trusted)",
        "-config", "tsa.cnf", "-extensions", "ca_ext")
    run("openssl", "req", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:P-256", "-nodes",
        "-keyout", "tsa.key", "-out", "tsa.csr", "-config", "tsa.cnf")
    run("openssl", "x509", "-req", "-in", "tsa.csr", "-CA", "ca.crt", "-CAkey", "ca.key", "-CAcreateserial",
        "-out", "tsa.crt", "-days", "36500", "-extfile", "tsa.cnf", "-extensions", "tsa_ext")
    (tsa_dir / "serial").write_text("01\n")
    return tsa_dir / "ca.crt"


# ---------------------------------------------------------------- bounds

def witness_holds(n, k, a, b, u, v, d) -> bool:
    """Mirror of `ChernoffWitness.binomCdf_le_of_witness`'s hypothesis."""
    return d * (b * v - a * v + a * u) ** n * v ** k <= (b * v) ** n * u ** k


def best_witness(n, k, a, b, prec=1 << 40):
    """Near-optimal t = u/v for p = a/b: t* = k(1-p) / ((n-k)p), clipped to (0, 1]."""
    p = a / b
    if k >= n or p == 0:
        return prec, prec
    t = min(1.0, k * (1 - p) / ((n - k) * p)) if k > 0 else 1.0 / prec
    return max(1, int(t * prec)), prec


def tightest_witness_bound(n, k, b, d):
    """Smallest a / b (to resolution 1/b) with a Chernoff witness the kernel accepts."""
    def ok(a):
        u, v = best_witness(n, k, a, b)
        return witness_holds(n, k, a, b, u, v, d)
    lo, hi = 0, b
    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo, best_witness(n, k, lo, b)


# ---------------------------------------------------------------- commands

def commit(args) -> None:
    pool = read_pool(args.pool)
    tree = merkle.levels([merkle.leaf_hash(merkle.canonical(x)) for x in pool])
    round_ = args.round
    if round_ is None:
        round_ = drand_get(args.chain, "public/latest")["round"] + args.rounds_ahead
    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    commitment = {
        "format": "opentheory-pool-commitment/0.1",
        "issuer": args.issuer,
        "pool": {"root": merkle.root(tree).hex(), "size": len(pool)},
        "procedure": {"kind": "exact-match"},
        "sample": {"n": args.n, "delta": {"num": 1, "den": args.delta_den}},
        "beacon": {"chain": args.chain, "round": round_},
    }
    if args.audit_m:
        commitment["procedure"]["kind"] = "judged-exact-match"
        audit = {"m": args.audit_m, "delta_missed": {"num": 1, "den": args.audit_delta_den}}
        if args.alarms_delta_den:
            audit["delta_alarms"] = {"num": 1, "den": args.alarms_delta_den}
        commitment["sample"]["audit"] = audit
    sha = write_json(out / "commitment.json", commitment)
    if args.tsa_url:
        token = tsa_url(sha, args.tsa_url)
    else:
        tsa_dir = args.test_tsa
        if not (tsa_dir / "tsa.cnf").exists():
            make_test_tsa(tsa_dir)
        token = tsa_local(sha, tsa_dir)
    (out / "order.tsr").write_bytes(token)
    print(f"committed pool root {commitment['pool']['root'][:16]}… (N = {len(pool)}), n = {args.n}, "
          f"δ = 1/{args.delta_den}, drand round {round_}")


def tightest(n: int, k: int, d: int, b: int, witness: bool = False) -> dict:
    """The tightest rate claim the decision procedure accepts for k of n set bits at δ = 1/d."""
    if k <= EXACT_TAIL_MAX_K and not witness:
        return {"count": k, "bound": {"num": binomial_bound.tightest_bound(n, k, b, d), "den": b}}
    a, (u, v) = tightest_witness_bound(n, k, b, d)
    return {"count": k, "bound": {"num": a, "den": b}, "witness": {"num": u, "den": v}}


def prove(args) -> None:
    cdir = args.commitment
    commitment = json.loads((cdir / "commitment.json").read_text())
    pool = read_pool(args.pool)
    size, n, d = commitment["pool"]["size"], commitment["sample"]["n"], commitment["sample"]["delta"]["den"]
    leaves = [merkle.leaf_hash(merkle.canonical(x)) for x in pool]
    tree = merkle.levels(leaves)
    if merkle.root(tree).hex() != commitment["pool"]["root"] or len(pool) != size:
        sys.exit("error: this pool does not match the commitment")
    chain, round_ = commitment["beacon"]["chain"], commitment["beacon"]["round"]
    beacon = json.loads(args.beacon.read_text()) if args.beacon else fetch_round(chain, round_)
    indices = derive_indices(round_, bytes.fromhex(beacon["signature"]), n, size)
    items = [{"index": idx, "leaf": pool[idx], "proof": [h.hex() for h in merkle.inclusion_proof(tree, idx)]}
             for idx in indices]
    same = lambda x, y: merkle.canonical(x) == merkle.canonical(y)
    b = args.scale
    sample = {"items": items}
    if commitment["procedure"]["kind"] == "judged-exact-match":
        audit = commitment["sample"]["audit"]
        m = audit["m"]
        gold_map = json.loads(args.gold.read_text())
        gold = [gold_map[str(idx)] for idx in indices[:m]]
        out_ = [pool[idx]["output"] for idx in indices]
        judged = [not same(o, pool[idx]["judge"]) for o, idx in zip(out_, indices)]
        fail = [not same(o, g) for o, g in zip(out_, gold)]
        missed = sum(f and not j for f, j in zip(fail, judged))
        alarms = sum((not f) and j for f, j in zip(fail, judged))
        claim = {"type": "judged-rate", "version": "0.1",
                 "judge": tightest(n, sum(judged), d, b, args.witness),
                 "audit": tightest(m, missed, audit["delta_missed"]["den"], b, args.witness)}
        bound = claim["judge"]["bound"]["num"] + claim["audit"]["bound"]["num"]
        if "delta_alarms" in audit:
            part = tightest(m, m - alarms, audit["delta_alarms"]["den"], b, args.witness)
            if part["bound"]["num"] < b:  # only when it lowers the bound
                claim["alarms"] = part
                bound += part["bound"]["num"] - b
        sample["gold"] = gold
        gold_only = binomial_bound.tightest_bound(m, sum(fail), b, d)
        summary = (f"judge: {sum(judged)}/{n}; gold on {m}: {sum(fail)} failures, {missed} missed, "
                   f"{alarms} false alarms; claim: true rate ≤ {bound / b:.4%} "
                   f"(gold labels alone, same m, δ = 1/{d}: ≤ {gold_only / b:.4%})")
    else:
        labels = json.loads(args.labels.read_text()) if args.labels else None
        sample_labels, fails = [], 0
        for idx in indices:
            leaf = pool[idx]
            label = leaf["label"] if "label" in leaf else labels[str(idx)]
            fails += not same(leaf["output"], label)
            sample_labels.append(label)
        if labels is not None:
            sample["labels"] = sample_labels
        claim = {"type": "pool-rate", "version": "0.1", "delta": {"num": 1, "den": d},
                 **tightest(n, fails, d, b, args.witness)}
        if args.claim_count is not None:
            claim["count"] = args.claim_count
        if args.claim_bound is not None:
            claim["bound"]["num"] = args.claim_bound
        summary = (f"{fails} failures in {n} sampled items; claim: pool rate ≤ {claim['bound']['num'] / b:.4%} "
                   f"with δ = 1/{d}" + (" (Chernoff witness)" if "witness" in claim else " (exact tail)"))

    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    shutil.copy(cdir / "commitment.json", out / "commitment.json")
    shutil.copy(cdir / "order.tsr", out / "order.tsr")
    ref = lambda name: {"path": name, "sha256": hashlib.sha256((out / name).read_bytes()).hexdigest()}
    write_json(out / "beacon.json", beacon)
    write_json(out / "sample.json", sample)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    cert = {
        "format": "opentheory-certificate/0.1",
        "claim": claim,
        "subject": {"commitment": ref("commitment.json")},
        "evidence": {"order": {"kind": "rfc3161", "token": ref("order.tsr")},
                     "beacon": ref("beacon.json"), "sample": ref("sample.json")},
        "assumptions": ASSUMPTIONS + (["A9-gold-labels"] if claim["type"] == "judged-rate" else []),
        "pins": {"lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(), "opentheory_commit": head},
    }
    write_json(out / "certificate.json", cert)
    print(summary)


def main(argv=None) -> None:
    p = argparse.ArgumentParser(prog="ot certify pool-rate", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("commit", help="commit to the pool before the beacon round")
    c.add_argument("--pool", type=Path, required=True, help="JSON lines, one pool item per line")
    c.add_argument("--n", type=int, required=True, help="sample size")
    c.add_argument("--delta-den", type=int, default=1000, help="δ = 1/d")
    c.add_argument("--issuer", required=True)
    c.add_argument("--chain", default=DEFAULT_CHAIN)
    c.add_argument("--round", type=int, help="drand round (default: latest + --rounds-ahead)")
    c.add_argument("--rounds-ahead", type=int, default=3)
    c.add_argument("--tsa-url", help="public RFC 3161 authority (sends only the commitment digest)")
    c.add_argument("--test-tsa", type=Path, default=Path(".ot-test-tsa"),
                   help="directory of a local TEST authority, created if missing")
    c.add_argument("--audit-m", type=int, help="judged-rate: gold labels on the first m sampled items")
    c.add_argument("--audit-delta-den", type=int, default=1000, help="judged-rate: δ of the missed part")
    c.add_argument("--alarms-delta-den", type=int, help="judged-rate: δ of the false-alarm part (optional)")
    c.add_argument("--out", type=Path, required=True)
    v = sub.add_parser("prove", help="after the round: write the certificate bundle")
    v.add_argument("--commitment", type=Path, required=True, help="directory written by commit")
    v.add_argument("--pool", type=Path, required=True)
    v.add_argument("--labels", type=Path, help="JSON {index: label} for items whose leaf has no label")
    v.add_argument("--gold", type=Path, help="judged-rate: JSON {index: gold label}")
    v.add_argument("--beacon", type=Path, help="recorded round (default: fetch from drand)")
    v.add_argument("--scale", type=int, default=100_000, help="bound resolution 1/scale")
    v.add_argument("--witness", action="store_true", help="always use a Chernoff witness")
    v.add_argument("--claim-count", type=int, help=argparse.SUPPRESS)  # tamper tests only
    v.add_argument("--claim-bound", type=int, help=argparse.SUPPRESS)
    v.add_argument("--out", type=Path, required=True)
    args = p.parse_args(argv)
    commit(args) if args.cmd == "commit" else prove(args)


if __name__ == "__main__":
    main()
