#!/usr/bin/env python3
"""Conformance for `ot verify` on `rate-gap` and `rate-ratio` v0.1 (two committed pools).

Rebuilds the synthetic pools of examples/rate_gap (seeded), proves honest gap and ratio bundles from
the recorded commitment, timestamp and drand round in fixtures/rate_gap/, derives forged bundles,
and checks that `ot verify` accepts exactly the honest ones, each forgery for the expected reason.
Same requirements as pool_rate_verify.py.

  python tests/conformance/rate_gap_verify.py [--fast]   # --fast: skip the compiled-lane duplicates
"""
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIX = ROOT / "tests/conformance/fixtures/rate_gap"
PRODUCER = ROOT / "methods/statistical/pool_rate_certificate.py"
sys.path.insert(0, str(Path(__file__).resolve().parent))
from pool_rate_verify import edit_cert, edit_json, forge_beacon, rehash, run  # noqa: E402


def part(name, **change):
    return lambda b: edit_cert(b, lambda c: c["claim"][name].update(change))


def b_item_in_a(bundle):
    """Replace pool A's first sampled item by pool B's first one (a valid item of the wrong pool)."""
    def f(s):
        s["items"][0] = s["items_b"][0]
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def flip_decision(bundle):
    """Rewrite a sampled decline in pool B as an approval, without recommitting."""
    def f(s):
        i = next(j for j, it in enumerate(s["items_b"]) if it["leaf"]["output"] == "decline")
        s["items_b"][i]["leaf"]["output"] = "approve"
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def drop_b(bundle):
    edit_json(bundle, "sample.json", lambda s: s["items_b"].pop())
    rehash(bundle, "evidence", "sample")


def main():
    try:
        import py_arkworks_bls12381  # noqa: F401
    except ImportError:
        try:
            import py_ecc  # noqa: F401
        except ImportError:
            print("rate-gap conformance needs py_arkworks_bls12381 or py_ecc. Not run.")
            return 2
    spec = importlib.util.spec_from_file_location("gap_make_pools", ROOT / "examples/rate_gap/make_pools.py")
    make_pools = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(make_pools)
    fast = "--fast" in sys.argv
    tmp = Path(tempfile.mkdtemp(prefix="ot-gap-conformance-"))
    roots = tmp / "roots"
    roots.mkdir()
    shutil.copy(FIX / "tsa_root.pem", roots / "test-root.pem")
    make_pools.make(tmp / "pools")
    commit = tmp / "commit"
    commit.mkdir()
    for f in ("commitment.json", "order.tsr"):
        shutil.copy(FIX / f, commit / f)
    for agg, out in (("gap", "honest"), ("ratio", "honest_ratio")):
        subprocess.run([sys.executable, str(PRODUCER), "prove", "--commitment", str(commit),
                        "--pool", str(tmp / "pools/pool_a.jsonl"), "--pool-b", str(tmp / "pools/pool_b.jsonl"),
                        "--aggregate", agg, "--c", "4/5", "--beacon", str(FIX / "beacon.json"), "--out", str(tmp / out)],
                       check=True, capture_output=True)

    # name: (mutation, base bundle, expected reason substring or None for accept, compiled lane)
    cases = {
        "honest_gap": (None, "honest", None, False),
        "honest_gap_compiled": (None, "honest", None, True),
        "honest_ratio": (None, "honest_ratio", None, False),
        "epsilon_below_certified": (lambda b: edit_cert(b, lambda c: c["claim"].update(epsilon={"num": 1, "den": 100})),
                                    "honest", "is below the gap the bounds certify", False),
        "ratio_not_certified": (lambda b: edit_cert(b, lambda c: c["claim"].update(c={"num": 1, "den": 1})),
                                "honest_ratio", "the ratio is not certified", False),
        "understated_count": (part("upperA", count=10), "honest", "upper A: ", False),
        "understated_count_compiled": (part("upperA", count=10), "honest", "upper A: ", True),
        "pool_b_item_in_pool_a": (b_item_in_a, "honest", "the beacon selects pool index", False),
        "decision_rewritten": (flip_decision, "honest", "Merkle inclusion fails", False),
        "pool_b_sample_short": (drop_b, "honest", "sample.items_b", False),
        "forged_beacon": (forge_beacon, "honest", "invalid drand signature", False),
        "claimed_as_pool_rate": (lambda b: edit_cert(b, lambda c: c["claim"].update(type="pool-rate")),
                                 "honest", "claim: missing", False),
    }
    selected = {n: c for n, c in cases.items() if not (fast and c[3])}
    for name, (mutate, base, _, _) in selected.items():
        if mutate is not None:
            shutil.copytree(tmp / base, tmp / name)
            mutate(tmp / name)
    target = lambda n: tmp / (cases[n][1] if cases[n][0] is None else n)
    with ThreadPoolExecutor(max_workers=4) as ex:
        results = dict(zip(selected, ex.map(lambda n: run(target(n), roots, cases[n][3]), selected)))
    failed = 0
    for name, (_, _, expect, compiled) in selected.items():
        r = results[name]
        ok = r["accepted"] if expect is None else (not r["accepted"] and expect in r.get("reason", ""))
        if r["accepted"]:
            ok = ok and (("not verified" in r.get("level", "")) if compiled else r.get("level") == "verified")
            ok = ok and any(a["id"] == "A10-group-membership" for a in r.get("assumptions", []))
        failed += not ok
        want = "accept" if expect is None else f"reject ({expect})"
        got = "accepted" if r["accepted"] else f"rejected: {r.get('reason', '')}"
        print(f"[{'ok' if ok else 'FAIL'}] {name}: expected {want}; {got[:220]}")
    for n in ("honest_gap", "honest_ratio"):
        if n in results and results[n]["accepted"]:
            print("\n  " + results[n]["claim"])
    shutil.rmtree(tmp)
    print(f"\n{len(selected) - failed}/{len(selected)} conformance cases pass")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
