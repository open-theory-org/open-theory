#!/usr/bin/env python3
"""Conformance for `ot verify` on `judged-rate` v0.1.

Rebuilds the synthetic judged pool of examples/judged_rate (seeded), proves an honest bundle from the
recorded commitment, timestamp and drand round in fixtures/judged_rate/, derives forged bundles,
and checks that `ot verify` accepts exactly the honest ones, each forgery for the expected reason.
Same requirements as pool_rate_verify.py.

  python tests/conformance/judged_rate_verify.py [--fast]   # --fast: skip the compiled-lane duplicates
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
FIX = ROOT / "tests/conformance/fixtures/judged_rate"
PRODUCER = ROOT / "methods/statistical/pool_rate_certificate.py"
sys.path.insert(0, str(Path(__file__).resolve().parent))
from pool_rate_verify import edit_cert, edit_json, forge_beacon, rehash, run  # noqa: E402


def drop_alarms(bundle):
    edit_cert(bundle, lambda c: c["claim"].pop("alarms"))


def part(name, **change):
    return lambda b: edit_cert(b, lambda c: c["claim"][name].update(change))


def tamper_judge_label(bundle):
    """Make the committed judge agree with a failing output, without recommitting."""
    def f(s):
        i = next(j for j, it in enumerate(s["items"]) if it["leaf"]["output"] != it["leaf"]["judge"])
        s["items"][i]["leaf"]["judge"] = s["items"][i]["leaf"]["output"]
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def short_gold(bundle):
    edit_json(bundle, "sample.json", lambda s: s["gold"].pop())
    rehash(bundle, "evidence", "sample")


def gold_from_outputs(bundle):
    """A dishonest labeller copies the outputs: every audited item passes. Accepted, under A9."""
    def f(s):
        s["gold"] = [it["leaf"]["output"] for it in s["items"][:len(s["gold"])]]
    edit_json(bundle, "sample.json", f)
    rehash(bundle, "evidence", "sample")


def as_pool_rate(bundle):
    edit_cert(bundle, lambda c: c["claim"].update(type="pool-rate", count=0, bound={"num": 1, "den": 2},
                                                  delta={"num": 1, "den": 2}))


def main():
    try:
        import py_arkworks_bls12381  # noqa: F401
    except ImportError:
        try:
            import py_ecc  # noqa: F401
        except ImportError:
            print("judged-rate conformance needs py_arkworks_bls12381 or py_ecc. Not run.")
            return 2
    spec = importlib.util.spec_from_file_location("judged_make_pool", ROOT / "examples/judged_rate/make_pool.py")
    make_pool = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(make_pool)
    fast = "--fast" in sys.argv
    tmp = Path(tempfile.mkdtemp(prefix="ot-judged-conformance-"))
    roots = tmp / "roots"
    roots.mkdir()
    shutil.copy(FIX / "tsa_root.pem", roots / "test-root.pem")
    make_pool.make(tmp / "pool")
    commit = tmp / "commit"
    commit.mkdir()
    for f in ("commitment.json", "order.tsr"):
        shutil.copy(FIX / f, commit / f)
    subprocess.run([sys.executable, str(PRODUCER), "prove", "--commitment", str(commit),
                    "--pool", str(tmp / "pool/pool.jsonl"), "--gold", str(tmp / "pool/gold.json"),
                    "--beacon", str(FIX / "beacon.json"), "--out", str(tmp / "honest")],
                   check=True, capture_output=True)
    if "alarms" not in json.loads((tmp / "honest/certificate.json").read_text())["claim"]:
        print("the honest bundle has no alarms part; the alarm cases below would not test it")
        return 1

    # name: (mutation, expected reason substring or None for accept, compiled lane)
    cases = {
        "honest": (None, None, False),
        "honest_compiled": (None, None, True),
        "without_alarms": (drop_alarms, None, False),
        "judge_count_understated": (part("judge", count=100), "judge: ", False),
        "judge_count_understated_compiled": (part("judge", count=100), "judge: ", True),
        "missed_bound_too_tight": (part("audit", bound={"num": 1, "den": 100000}), "audit: ", False),
        "alarms_bound_too_tight": (part("alarms", bound={"num": 90000, "den": 100000}), "alarms: ", False),
        "judge_label_changed_after_commit": (tamper_judge_label, "Merkle inclusion fails", False),
        "gold_labels_missing": (short_gold, "sample.gold must be a list of", False),
        "forged_beacon": (forge_beacon, "invalid drand signature", False),
        "claimed_as_pool_rate": (as_pool_rate, "this claim type needs", False),
        "gold_copied_from_outputs": (gold_from_outputs, None, False),
    }
    selected = {n: c for n, c in cases.items() if not (fast and c[2])}
    for name, (mutate, _, _) in selected.items():
        if mutate is not None:
            shutil.copytree(tmp / "honest", tmp / name)
            mutate(tmp / name)
    target = lambda n: tmp / ("honest" if cases[n][0] is None else n)
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
        if name == "gold_copied_from_outputs":
            ok = ok and any("A9-gold-labels" == a["id"] for a in r.get("assumptions", []))
        failed += not ok
        want = "accept" if expect is None else f"reject ({expect})"
        got = "accepted" if r["accepted"] else f"rejected: {r.get('reason', '')}"
        print(f"[{'ok' if ok else 'FAIL'}] {name}: expected {want}; {got[:220]}")
    if "honest" in results and results["honest"]["accepted"]:
        print("\n  " + results["honest"]["claim"])
    shutil.rmtree(tmp)
    print(f"\n{len(selected) - failed}/{len(selected)} conformance cases pass")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
