#!/usr/bin/env python3
"""Conformance for `ot verify` on `pool-rate` v0.1.

Rebuilds the synthetic 100,000-item pool of examples/pool_rate (seeded), proves an honest bundle
from the recorded commitment, timestamp and drand round in fixtures/pool_rate/, derives forged
bundles, and checks that `ot verify` accepts exactly the honest ones, each forgery for the
expected reason, with the Lean kernel (the default, `verified` lane) and, for cases marked
compiled, with the compiled decision procedure (`--compiled`). The recorded timestamp comes from a local TEST authority, trusted here only through
$OT_TSA_ROOTS. Needs `lake build`, `lake build ot_check`, `openssl`, and `py_arkworks_bls12381`
or `py_ecc` (run with a Python that has one).

  python tests/conformance/pool_rate_verify.py [--fast]   # --fast: skip the compiled-lane duplicates
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OT = ROOT / "interfaces/cli/ot"
FIX = ROOT / "tests/conformance/fixtures/pool_rate"
PRODUCER = ROOT / "methods/statistical/pool_rate_certificate.py"
sys.path.insert(0, str(ROOT / "examples/pool_rate"))
sys.path.insert(0, str(ROOT / "methods/statistical"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rehash(bundle, *ref):
    cert = json.loads((bundle / "certificate.json").read_text())
    node = cert
    for key in ref:
        node = node[key]
    node["sha256"] = sha(bundle / node["path"])
    (bundle / "certificate.json").write_text(json.dumps(cert))


def edit_json(bundle, name, f):
    p = bundle / name
    obj = json.loads(p.read_text())
    f(obj)
    p.write_text(json.dumps(obj, separators=(",", ":")))


def edit_cert(bundle, f):
    edit_json(bundle, "certificate.json", f)


def cherry_pick(bundle, pool, tree, merkle):
    """Replace a sampled failure by a pool item the beacon did not select, with a valid proof."""
    def f(s):
        i = next(j for j, it in enumerate(s["items"]) if it["leaf"]["output"] != s["labels"][j])
        good = next(j for j in range(len(pool)) if j not in {it["index"] for it in s["items"]})
        s["items"][i] = {"index": good, "leaf": pool[good],
                         "proof": [h.hex() for h in merkle.inclusion_proof(tree, good)]}
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def hide_failure(bundle):
    """Keep the selected index but rewrite the logged output to the label."""
    def f(s):
        i = next(j for j, it in enumerate(s["items"]) if it["leaf"]["output"] != s["labels"][j])
        s["items"][i]["leaf"]["output"] = s["labels"][i]
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def flip_labels(bundle):
    """Labels supplied after sampling are trusted: set them all to the outputs."""
    def f(s):
        s["labels"] = [it["leaf"]["output"] for it in s["items"]]
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")
    edit_cert(bundle, lambda c: c["claim"].update(count=0))


def forge_beacon(bundle):
    edit_json(bundle, "beacon.json", lambda b: b.update(signature=("00" if b["signature"][:2] != "00" else "11")
                                                         + b["signature"][2:]))
    rehash(bundle, "evidence", "beacon")


def other_round(bundle):
    edit_json(bundle, "beacon.json", lambda b: b.update(round=b["round"] + 1))
    rehash(bundle, "evidence", "beacon")


def edit_commitment(bundle):
    edit_json(bundle, "commitment.json", lambda c: c["sample"].update(n=c["sample"]["n"] - 1))
    rehash(bundle, "subject", "commitment")


def restamp(bundle, tsa_dir, trusted_roots=None):
    """Timestamp the commitment again now, with a fresh test authority."""
    import pool_rate_certificate as P
    P.make_test_tsa(tsa_dir)
    (bundle / "order.tsr").write_bytes(P.tsa_local(sha(bundle / "commitment.json"), tsa_dir))
    rehash(bundle, "evidence", "order", "token")
    if trusted_roots is not None:
        shutil.copy(tsa_dir / "ca.crt", trusted_roots / "late-test-root.pem")


def add_attempt(bundle, issuer):
    c = json.loads((bundle / "commitment.json").read_text())
    c["issuer"] = issuer
    c["pool"]["root"] = "ab" * 32
    (bundle / "attempt.json").write_text(json.dumps(c, separators=(",", ":")))
    edit_cert(bundle, lambda x: x["evidence"].update(attempts=[{"path": "attempt.json",
                                                                "sha256": sha(bundle / "attempt.json")}]))


def drop_item(bundle):
    edit_json(bundle, "sample.json", lambda s: (s["items"].pop(), s["labels"].pop()))
    rehash(bundle, "evidence", "sample")


def run(bundle, roots, compiled=False):
    env = dict(os.environ, OT_TSA_ROOTS=str(roots))
    res = subprocess.run([sys.executable, str(OT), "verify", str(bundle), "--json", *(["--compiled"] if compiled else [])],
                         capture_output=True, text=True, env=env)
    try:
        return json.loads(res.stdout)
    except json.JSONDecodeError:
        return {"accepted": False, "reason": f"verifier could not run: {res.stdout[-300:]}{res.stderr[-300:]}"}


def main():
    try:
        import py_arkworks_bls12381  # noqa: F401
    except ImportError:
        try:
            import py_ecc  # noqa: F401
        except ImportError:
            print("pool-rate conformance needs py_arkworks_bls12381 or py_ecc. Not run.")
            return 2
    import make_pool
    fast = "--fast" in sys.argv
    tmp = Path(tempfile.mkdtemp(prefix="ot-pool-conformance-"))
    roots = tmp / "roots"
    roots.mkdir()
    shutil.copy(FIX / "tsa_root.pem", roots / "test-root.pem")
    make_pool.make(tmp / "pool")
    commit = tmp / "commit"
    commit.mkdir()
    for f in ("commitment.json", "order.tsr"):
        shutil.copy(FIX / f, commit / f)
    prove = lambda out, *extra: subprocess.run(
        [sys.executable, str(PRODUCER), "prove", "--commitment", str(commit), "--pool", str(tmp / "pool/pool.jsonl"),
         "--labels", str(tmp / "pool/labels.json"), "--beacon", str(FIX / "beacon.json"), "--out", str(out), *extra],
        check=True, capture_output=True)
    prove(tmp / "honest")
    prove(tmp / "witness", "--witness")

    import pool_rate_certificate as P
    pool = P.read_pool(tmp / "pool/pool.jsonl")
    tree = P.merkle.levels([P.merkle.leaf_hash(P.merkle.canonical(x)) for x in pool])
    if P.merkle.root(tree).hex() != json.loads((FIX / "commitment.json").read_text())["pool"]["root"]:
        print("the regenerated pool does not match the recorded commitment (make_pool changed?)")
        return 1

    count20 = lambda b: edit_cert(b, lambda c: c["claim"].update(count=20))
    # name: (mutation, expected reason substring or None for accept, compiled lane)
    cases = {
        "honest": (None, None, False),
        "honest_compiled": ("honest", None, True),
        "chernoff_witness": ("witness", None, False),
        "chernoff_witness_compiled": ("witness", None, True),
        "understated_count": (count20, "more than the claimed 20", False),
        "understated_count_compiled": (count20, "more than the claimed 20", True),
        "bound_too_tight": (lambda b: edit_cert(b, lambda c: c["claim"]["bound"].update(num=1500)),
                            "does not support the bound", False),
        "useless_witness": (lambda b: edit_cert(b, lambda c: c["claim"].update(witness={"num": 1, "den": 1})),
                            "does not support the bound", False),
        "useless_witness_compiled": (lambda b: edit_cert(b, lambda c: c["claim"].update(witness={"num": 1, "den": 1})),
                                   "does not support the bound", True),
        "declared_second_attempt": (lambda b: add_attempt(b, json.loads((FIX / "commitment.json").read_text())["issuer"]),
                                    None, False),
        "labels_after_sampling_flipped": (flip_labels, None, False),
        "cherry_picked_item": (lambda b: cherry_pick(b, pool, tree, P.merkle), "the beacon selects pool index", False),
        "hidden_failure": (hide_failure, "Merkle inclusion fails", False),
        "dropped_item": (drop_item, "the commitment fixes", False),
        "forged_beacon": (forge_beacon, "invalid drand signature", False),
        "other_round": (other_round, "differs from the committed round", False),
        "commitment_edited_after_stamp": (edit_commitment, "timestamp token is invalid", False),
        "untrusted_timestamp_authority": (lambda b: restamp(b, tmp / "tsa-untrusted"), "timestamp token is invalid", False),
        "commitment_after_round": (lambda b: restamp(b, tmp / "tsa-late", roots), "not before round", False),
        "delta_changed_after_commit": (lambda b: edit_cert(b, lambda c: c["claim"].update(delta={"num": 1, "den": 1000})),
                                       "must equal the committed delta", False),
        "no_order_evidence": (lambda b: edit_cert(b, lambda c: c["evidence"].update(order={"kind": "none"})),
                              "precedes the beacon round", False),
        "attempt_by_other_issuer": (lambda b: add_attempt(b, "someone-else"), "not a commitment by the same issuer", False),
        "path_escape": (lambda b: edit_cert(b, lambda c: c["evidence"]["sample"].update(path="../honest/sample.json")),
                        "escapes the bundle", False),
    }
    selected = {n: c for n, c in cases.items() if not (fast and c[2])}
    for name, (mutate, _, _) in selected.items():
        if mutate in (None, "honest", "witness"):
            continue
        shutil.copytree(tmp / "honest", tmp / name)
        mutate(tmp / name)
    target = lambda n: tmp / {None: "honest", "honest": "honest", "witness": "witness"}.get(cases[n][0], n) \
        if not callable(cases[n][0]) else tmp / n
    with ThreadPoolExecutor(max_workers=4) as ex:
        results = dict(zip(selected, ex.map(lambda n: run(target(n), roots, cases[n][2]), selected)))
    failed = 0
    for name, (_, expect, _) in selected.items():
        r = results[name]
        ok = r["accepted"] if expect is None else (not r["accepted"] and expect in r.get("reason", ""))
        if cases[name][2] and r["accepted"]:
            ok = ok and "not verified" in r.get("level", "")
        elif r["accepted"]:
            ok = ok and r.get("level") == "verified"
        if name == "declared_second_attempt":
            ok = ok and "total δ = 1/500000" in " ".join(r.get("checked", [])) and "2 declared" in r.get("claim", "")
        if name == "labels_after_sampling_flipped":
            ok = ok and any("supplied after sampling" in t for t in r.get("trusted", []))
        failed += not ok
        want = "accept" if expect is None else f"reject ({expect})"
        got = "accepted" if r["accepted"] else f"rejected: {r.get('reason', '')}"
        print(f"[{'ok' if ok else 'FAIL'}] {name}: expected {want}; {got}")
    shutil.rmtree(tmp)
    print(f"\n{len(selected) - failed}/{len(selected)} conformance cases pass")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
