"""Claim types `pool-rate` and `judged-rate` v0.1 (specs/claims/pool-rate.md, judged-rate.md).

The bundle carries data only. Both handlers
  1. check that the commitment was timestamped before the beacon round (RFC 3161, trusted roots
     chosen by whoever runs the verifier),
  2. check the beacon round's signature on a pinned drand chain,
  3. recompute every sampled index from the round signature and check each sampled item's Merkle
     inclusion in the committed pool,
  4. compute the sampled bits with the committed procedure,
  5. run the registered check `OpenTheory.Checks.poolCheck` on each bit vector, in the kernel
     (`ot_kernel`; or compiled with `--compiled`, which is not `verified`); its meaning is proved once,
  6. sum δ over every commitment the issuer declares for the same round.
The Lean theorems `DesignSampling.rate_sound` (`pool-rate`) and `JudgedRate.bad_frac` with
`JudgedRate.Claim.sound` (`judged-rate`) turn 1–5 into the guarantee. Steps 1–4 and 6 are this
file's code, listed as trusted.
"""
from __future__ import annotations

import hashlib
import importlib.util
import re
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

from . import merkle
from .engine import ROOT, Reject, require
from .heldout_error import Task, parse_fraction

DOMAIN = b"opentheory/pool-rate/v0.1"
COMMITMENT_FORMAT = "opentheory-pool-commitment/0.1"
PROCEDURES = ("exact-match", "judged-exact-match")
MAX_N = 50_000  # v0.1: bundle size (one inclusion proof per item) and kernel-mode budget
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def derive_indices(round_: int, signature: bytes, n: int, size: int) -> list[int]:
    """Block `i` is SHA-256(DOMAIN ‖ round ‖ signature ‖ i) read big-endian; the index is it mod size."""
    head = DOMAIN + round_.to_bytes(8, "big") + signature
    return [int.from_bytes(hashlib.sha256(head + i.to_bytes(8, "big")).digest(), "big") % size
            for i in range(n)]


def attestation(name: str):
    """Load verifier/attestations/<name>.py by path (the verifier never edits sys.path)."""
    mod = f"opentheory_attest_{name}"
    if mod not in sys.modules:
        spec = importlib.util.spec_from_file_location(mod, ROOT / "verifier" / "attestations" / f"{name}.py")
        m = importlib.util.module_from_spec(spec)
        sys.modules[mod] = m
        spec.loader.exec_module(m)
    return sys.modules[mod]


def load_bytes(bundle: Path, ref: dict, where: str) -> tuple[bytes, str]:
    rel = require(ref, "path", str, where)
    digest = require(ref, "sha256", str, where)
    path = (bundle / rel).resolve()
    if bundle.resolve() not in path.parents:
        raise Reject(f"{where}.path escapes the bundle: {rel}")
    if not path.is_file():
        raise Reject(f"{where}.path not found: {rel}")
    data = path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != digest:
        raise Reject(f"{where}: sha256 mismatch for {rel} (certificate {digest[:12]}…, file {actual[:12]}…)")
    return data, actual


def one_over(obj, where: str) -> int:
    dn, d = parse_fraction(obj, where)
    if dn != 1 or d < 2:
        raise Reject(f"{where} must be 1/d with d ≥ 2")
    return d


def parse_commitment(c: dict, where: str) -> dict:
    if c.get("format") != COMMITMENT_FORMAT:
        raise Reject(f"{where}.format must be '{COMMITMENT_FORMAT}'")
    issuer = require(c, "issuer", str, where)
    pool = require(c, "pool", dict, where)
    root_hex = require(pool, "root", str, f"{where}.pool")
    size = require(pool, "size", int, f"{where}.pool")
    if not HEX64.match(root_hex) or size < 1:
        raise Reject(f"{where}.pool: need a 64-hex-digit root and size ≥ 1")
    proc = require(c, "procedure", dict, where)
    kind = require(proc, "kind", str, f"{where}.procedure")
    if kind not in PROCEDURES:
        raise Reject(f"{where}.procedure.kind must be one of {', '.join(PROCEDURES)}")
    sample = require(c, "sample", dict, where)
    n = require(sample, "n", int, f"{where}.sample")
    if not 1 <= n <= MAX_N:
        raise Reject(f"{where}.sample.n must be in [1, {MAX_N}]")
    d = one_over(require(sample, "delta", dict, f"{where}.sample"), f"{where}.sample.delta")
    out = {"issuer": issuer, "root": bytes.fromhex(root_hex), "size": size, "procedure": kind,
           "n": n, "d": d, "total": Fraction(1, d)}
    if kind == "judged-exact-match":
        audit = require(sample, "audit", dict, f"{where}.sample")
        m = require(audit, "m", int, f"{where}.sample.audit")
        if not 1 <= m <= n:
            raise Reject(f"{where}.sample.audit.m must be in [1, n]")
        dA = one_over(require(audit, "delta_missed", dict, f"{where}.sample.audit"),
                      f"{where}.sample.audit.delta_missed")
        dB = None
        if "delta_alarms" in audit:
            dB = one_over(audit["delta_alarms"], f"{where}.sample.audit.delta_alarms")
        out.update(m=m, dA=dA, dB=dB, total=Fraction(1, d) + Fraction(1, dA) + (Fraction(1, dB) if dB else 0))
    beacon = require(c, "beacon", dict, where)
    chain = require(beacon, "chain", str, f"{where}.beacon")
    round_ = require(beacon, "round", int, f"{where}.beacon")
    if chain not in attestation("drand").CHAINS:
        raise Reject(f"{where}.beacon.chain {chain[:16]}… is not a drand chain this verifier pins")
    if round_ < 1:
        raise Reject(f"{where}.beacon.round must be ≥ 1")
    out.update(chain=chain, round=round_)
    return out


def check_protocol(bundle: Path, cert: dict, load_file, kind: str):
    """Steps 1–3 and 6. Returns the commitment, the verified sampled leaves, the sample file, the
    report lines, and the attempt accounting (count, total δ)."""
    subject = require(cert, "subject", dict, "certificate")
    commitment, commitment_sha = load_file(bundle, require(subject, "commitment", dict, "subject"),
                                           "subject.commitment")
    c = parse_commitment(commitment, "commitment")
    if c["procedure"] != kind:
        raise Reject(f"commitment.procedure.kind is '{c['procedure']}', this claim type needs '{kind}'")
    evidence = require(cert, "evidence", dict, "certificate")

    # 1. Order: the commitment was timestamped before the round was published.
    order = require(evidence, "order", dict, "evidence")
    if require(order, "kind", str, "evidence.order") != "rfc3161":
        raise Reject("evidence.order.kind must be 'rfc3161': these claims need evidence that the "
                     "commitment precedes the beacon round")
    token, _ = load_bytes(bundle, require(order, "token", dict, "evidence.order"), "evidence.order.token")
    rfc, drand = attestation("rfc3161"), attestation("drand")
    try:
        ok, when, tsa = rfc.check(token, commitment_sha)
    except rfc.BackendUnavailable as e:
        raise RuntimeError(str(e))
    if not ok:
        raise Reject(f"evidence.order: the timestamp token is invalid ({tsa})")
    published = drand.round_time(c["chain"], c["round"])
    if when.timestamp() >= published:
        raise Reject(f"the commitment was timestamped at {when:%Y-%m-%d %H:%M:%S} UTC, not before round "
                     f"{c['round']} was published ({datetime.fromtimestamp(published, timezone.utc):%Y-%m-%d %H:%M:%S} UTC)")

    # 2. The beacon round.
    beacon, _ = load_file(bundle, require(evidence, "beacon", dict, "evidence"), "evidence.beacon")
    if require(beacon, "round", int, "beacon") != c["round"]:
        raise Reject(f"beacon.round {beacon['round']} differs from the committed round {c['round']}")
    try:
        sig = bytes.fromhex(require(beacon, "signature", str, "beacon"))
        prev = bytes.fromhex(require(beacon, "previous_signature", str, "beacon"))
    except ValueError:
        raise Reject("beacon: signatures must be hex")
    try:
        if not drand.verify_round(c["chain"], c["round"], sig, prev):
            raise Reject(f"beacon: invalid drand signature for round {c['round']}")
    except drand.BackendUnavailable as e:
        raise RuntimeError(str(e))

    # 3. The sample: recomputed indices and Merkle inclusion in the committed pool.
    sample, _ = load_file(bundle, require(evidence, "sample", dict, "evidence"), "evidence.sample")
    items = require(sample, "items", list, "sample")
    n, size = c["n"], c["size"]
    if len(items) != n:
        raise Reject(f"sample: {len(items)} items, the commitment fixes n = {n}")
    leaves = []
    for i, (item, idx) in enumerate(zip(items, derive_indices(c["round"], sig, n, size))):
        where = f"sample.items[{i}]"
        if not isinstance(item, dict):
            raise Reject(f"{where} must be an object")
        if require(item, "index", int, where) != idx:
            raise Reject(f"{where}.index is {item['index']}, but the beacon selects pool index {idx}")
        try:
            proof = [bytes.fromhex(h) for h in require(item, "proof", list, where)]
        except (TypeError, ValueError):
            raise Reject(f"{where}.proof must be hex strings")
        leaf = item.get("leaf")
        if not merkle.verify_inclusion(idx, size, merkle.leaf_hash(merkle.canonical(leaf)), proof, c["root"]):
            raise Reject(f"{where}: not the committed pool item at index {idx} (Merkle inclusion fails)")
        if not isinstance(leaf, dict) or "output" not in leaf:
            raise Reject(f"{where}.leaf: the procedure needs an object with 'output'")
        leaves.append(leaf)

    # 6. Attempt accounting: every commitment the issuer declares for this round.
    attempts, total = [commitment_sha], c["total"]
    for j, ref in enumerate(evidence.get("attempts", [])):
        other, sha = load_file(bundle, ref, f"evidence.attempts[{j}]")
        oc = parse_commitment(other, f"attempts[{j}]")
        if (oc["issuer"], oc["chain"], oc["round"]) != (c["issuer"], c["chain"], c["round"]):
            raise Reject(f"evidence.attempts[{j}] is not a commitment by the same issuer to the same round")
        if sha in attempts:
            raise Reject(f"evidence.attempts[{j}] repeats a commitment")
        attempts.append(sha)
        total += oc["total"]

    checked = [
        f"commitment sha256:{commitment_sha[:16]}… timestamped {when:%Y-%m-%d %H:%M:%S} UTC by {tsa}, "
        f"before round {c['round']} (RFC 3161, verifier's trusted roots)",
        f"drand round {c['round']} signature on the pinned chain {drand.CHAINS[c['chain']]['name']} "
        f"(BLS, {drand.backend()})",
        f"{n} indices recomputed from the round signature; each item's Merkle inclusion in pool root "
        f"{c['root'].hex()[:16]}… (N = {size})",
    ]
    return c, leaves, sample, checked, (len(attempts), total)


def same(a, b) -> bool:
    return merkle.canonical(a) == merkle.canonical(b)


# ---------------------------------------------------------------- the decision procedure

def parse_part(obj, where: str):
    """A rate claim: count `k`, bound `num/den`, optional Chernoff witness `u/v`."""
    k = require(obj, "count", int, where)
    if k < 0:
        raise Reject(f"{where}.count must be non-negative")
    num, den = parse_fraction(require(obj, "bound", dict, where), f"{where}.bound")
    witness = None
    if "witness" in obj:
        u, v = parse_fraction(require(obj, "witness", dict, where), f"{where}.witness")
        if u == 0:
            raise Reject(f"{where}.witness must be in (0, 1]")
        witness = (u, v)
    return k, num, den, witness


def levels(n: int) -> int:
    """Halving depth `l` with `n ≤ 64 · 2ˡ`, the witness `Checks.poolCheck` verifies."""
    return max(0, ((n + 63) // 64 - 1).bit_length())


def check_args(bits: list[bool], part, d: int) -> list[str]:
    """A request for `Checks.poolCheck` / `poolCheckWitness` (registry names `pool`, `pool-witness`)."""
    k, num, den, witness = part
    n = len(bits)
    x = hex(sum(1 << i for i, bit in enumerate(bits) if bit))
    if witness is None:
        return ["pool", x, str(n), str(levels(n)), str(k), str(num), str(den), str(d)]
    return ["pool-witness", x, str(n), str(levels(n)), str(k), str(num), str(den),
            str(witness[0]), str(witness[1]), str(d)]


def holds(bits: list[bool], part, d: int) -> bool:
    """Python reading of the check, used only to word a rejection; the compiled or kernel check decides."""
    from math import comb
    k, a, b, witness = part
    n = len(bits)
    if sum(bits) > k:
        return False
    if witness is None:
        return d * sum(comb(n, i) * a ** i * (b - a) ** max(n - i, 0) for i in range(k + 1)) <= b ** n
    u, v = witness
    return d * (b * v - a * v + a * u) ** n * v ** k <= (b * v) ** n * u ** k


def why_false(name: str, bits: list[bool], part, d: int) -> str:
    k, num, den, _ = part
    ones = sum(bits)
    if ones > k:
        return f"{name}: {ones} sampled items are set, more than the claimed {k}"
    return (f"{name}: the sample does not support the bound {num}/{den}: the tail inequality for "
            f"P(Bin({len(bits)}, {num}/{den}) ≤ {k}) ≤ 1/{d} is false")


def describe(part, d: int, n: int) -> str:
    k, num, den, witness = part
    fn = "poolCheck" if witness is None else "poolCheckWitness"
    tail = "exact tail" if witness is None else f"Chernoff witness t = {witness[0]}/{witness[1]}"
    return f"{fn}(n = {n}, k = {k}, p = {num}/{den}, δ = 1/{d}; {tail})"


SLACK = lambda n, size: (2 * n * size).bit_length() - 256  # (1 + N/2^256)^n ≤ 1 + 2^SLACK


def first_false(named: list[tuple[str, list[bool], tuple, int]]) -> str:
    return next((why_false(*x) for x in named if not holds(x[1], x[2], x[3])), "the decision procedure is false")


# ---------------------------------------------------------------- pool-rate

def handle(bundle: Path, cert: dict, load_file) -> Task:
    claim = cert["claim"]
    if require(claim, "version", str, "claim") != "0.1":
        raise Reject("claim.version must be '0.1'")
    part = parse_part(claim, "claim")
    c, leaves, sample, checked, (count, total) = check_protocol(bundle, cert, load_file, "exact-match")
    if one_over(require(claim, "delta", dict, "claim"), "claim.delta") != c["d"]:
        raise Reject(f"claim.delta must equal the committed delta 1/{c['d']}")
    n, size, d = c["n"], c["size"], c["d"]
    labels = sample.get("labels")
    if labels is not None and (not isinstance(labels, list) or len(labels) != n):
        raise Reject("sample.labels must be a list with one label per item")
    bits, labels_after = [], False
    for i, leaf in enumerate(leaves):
        if "label" in leaf:
            label = leaf["label"]
        elif labels is not None:
            label, labels_after = labels[i], True
        else:
            raise Reject(f"sample.items[{i}]: no label in the leaf and none supplied in sample.labels")
        bits.append(not same(leaf["output"], label))

    k, num, den, witness = part
    ones = sum(bits)
    args = check_args(bits, part, d)
    fn = "poolCheck" if args[0] == "pool" else "poolCheckWitness"
    checked += [f"{n} bits recomputed with 'exact-match' (verifier): {ones} set",
                f"attempt accounting over {count} declared commitment(s): total δ = {total}"]
    trusted = [
        "statements of OpenTheory.Checks.poolCheck, PoolRate.Claim.of_poolCheck, DesignSampling.rate_sound "
        "and selective_sound",
        "this verifier's index derivation, Merkle and exact-match code (verifier/core/pool_rate.py, merkle.py)",
        "SHA-256 as a random oracle for the beacon expansion (A5-beacon)",
    ]
    if labels_after:
        trusted.append("labels of the sampled items, supplied after sampling: the bound holds if they are the "
                       "labels a rule fixed before the round would give (they were not committed)")
    reason = lambda: why_false("claim", bits, part, d)
    return Task(
        lean="",
        theorem="",
        guarantee="pool-rate-exact-match",
        words=(f"At most {num / den:.4%} of the {size} committed pool items fail the procedure 'exact-match' "
               f"(logged output ≠ label, canonical JSON). Wrong with probability ≤ {float(total):.3g} "
               f"(+2^{SLACK(n, size)}) over the drand round, summed over the issuer's {count} declared "
               f"commitment(s) to round {c['round']}. Observed {ones} failure(s) in {n} sampled items."),
        checked=checked,
        trusted=trusted,
        does_not_cover=[
            "items outside the committed pool (other traffic, future traffic, distribution shift)",
            "whether the labels are correct: the rate is relative to them",
            "commitments the issuer made to the same round and did not declare (A7-issuer-identity)",
        ],
        fast=args,
        fast_call=f"OpenTheory.Checks.{describe(part, d, n)}",
        fast_meaning=(f"meaning, proved once: OpenTheory.PoolRate.Claim.of_{fn} turns it into "
                      f"Claim (bitsOf x {n}) {k} ({num}/{den}) (1/{d}), and DesignSampling.rate_sound "
                      "into the bound over seeds"),
        fast_explain=reason,
    )


# ---------------------------------------------------------------- judged-rate

def handle_judged(bundle: Path, cert: dict, load_file) -> Task:
    claim = cert["claim"]
    if require(claim, "version", str, "claim") != "0.1":
        raise Reject("claim.version must be '0.1'")
    judge = parse_part(require(claim, "judge", dict, "claim"), "claim.judge")
    audit = parse_part(require(claim, "audit", dict, "claim"), "claim.audit")
    alarms = parse_part(claim["alarms"], "claim.alarms") if "alarms" in claim else None
    c, leaves, sample, checked, (count, total) = check_protocol(bundle, cert, load_file, "judged-exact-match")
    n, m, size = c["n"], c["m"], c["size"]
    if alarms is not None and c["dB"] is None:
        raise Reject("claim.alarms needs commitment.sample.audit.delta_alarms")
    gold = sample.get("gold")
    if not isinstance(gold, list) or len(gold) != m:
        raise Reject(f"sample.gold must be a list of {m} gold labels, for the first {m} sampled items")
    for i, leaf in enumerate(leaves):
        if "judge" not in leaf:
            raise Reject(f"sample.items[{i}].leaf: judged-exact-match needs the committed 'judge' label")
    judged = [not same(leaf["output"], leaf["judge"]) for leaf in leaves]
    fail = [not same(leaf["output"], g) for leaf, g in zip(leaves, gold)]
    missed = [f and not j for f, j in zip(fail, judged)]
    not_alarm = [not ((not f) and j) for f, j in zip(fail, judged)]

    named = [("judge", judged, judge, c["d"]), ("audit", missed, audit, c["dA"])]
    if alarms is not None:
        named.append(("alarms", not_alarm, alarms, c["dB"]))
    groups = [check_args(bits, part, d) for _, bits, part, d in named]
    args = [a for g in groups for a in (*g, "+")][:-1]
    bound = Fraction(judge[1], judge[2]) + Fraction(audit[1], audit[2])
    if alarms is not None:
        bound += Fraction(alarms[1], alarms[2]) - 1
    used = Fraction(1, c["d"]) + Fraction(1, c["dA"]) + (Fraction(1, c["dB"]) if alarms is not None else 0)
    theorem = "Claim.sound_alarms" if alarms is not None else "Claim.sound"
    checked += [
        f"{n} judge verdicts recomputed (output ≠ committed judge label): {sum(judged)} failures",
        f"first {m} items graded against the supplied gold labels: {sum(fail)} failures, "
        f"{sum(missed)} missed by the judge, {m - sum(not_alarm)} false alarms",
        f"attempt accounting over {count} declared commitment(s): total δ = {total} (this claim uses {used})",
    ]
    reason = lambda: first_false(named)
    return Task(
        lean="",
        theorem="",
        guarantee="judged-rate-exact-match",
        words=(f"At most {float(bound):.4%} of the {size} committed pool items fail against gold labels "
               f"(logged output ≠ gold, canonical JSON), from judge verdicts on {n} sampled items and gold "
               f"labels on {m} of them. Wrong with probability ≤ {float(total):.3g} (+2^{SLACK(n, size)}) over "
               f"the drand round, summed over the issuer's {count} declared commitment(s) to round {c['round']}. "
               f"Gold-only estimate on the {m} audited items: {sum(fail)}/{m} = {sum(fail) / m:.2%}."),
        checked=checked,
        trusted=[
            "statements of OpenTheory.Checks.poolCheck, PoolRate.Claim.of_poolCheck, JudgedRate.Claim.sound, "
            "Claim.sound_alarms and JudgedRate.bad_frac",
            "this verifier's index derivation, Merkle and exact-match code (verifier/core/pool_rate.py, merkle.py)",
            "SHA-256 as a random oracle for the beacon expansion (A5-beacon)",
        ],
        does_not_cover=[
            "items outside the committed pool (other traffic, future traffic, distribution shift)",
            "whether the gold labels are correct: the rate is relative to them (A9-gold-labels)",
            "commitments the issuer made to the same round and did not declare (A7-issuer-identity)",
        ],
        fast=args,
        fast_call="OpenTheory.Checks: " + "; ".join(
            f"{nm}: {describe(part, d, len(bits))}" for nm, bits, part, d in named),
        fast_meaning=(f"meaning, proved once: PoolRate.Claim.of_poolCheck on each part, then "
                      f"JudgedRate.{theorem} gives true rate ≤ {bound} unless the seed is in JudgedRate.bad, "
                      "whose fraction JudgedRate.bad_frac bounds"),
        fast_explain=reason,
    )


HANDLERS = {"pool-rate": handle, "judged-rate": handle_judged}
