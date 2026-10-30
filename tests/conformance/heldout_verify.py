#!/usr/bin/env python3
"""Conformance for `ot verify` on `heldout-error` v0.1.

Builds an honest bundle from the digits artifact, derives forged bundles from it, and checks
that `ot verify` accepts exactly the honest one, each forgery for the expected reason.
Kernel cases run in parallel (about 3 minutes in total). Requires `lake build`.

  python3 tests/conformance/heldout_verify.py [--fast]   # --fast: skip the kernel cases
"""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OT = ROOT / "interfaces/cli/ot"
ARTIFACT = ROOT / "examples/certified_accuracy/model/pacbayes_digits64.json"


def rehash(bundle, ref):
    """Update a file digest in certificate.json, as a forger would."""
    cert = json.loads((bundle / "certificate.json").read_text())
    section, key = ref
    path = bundle / cert[section][key]["path"]
    cert[section][key]["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    (bundle / "certificate.json").write_text(json.dumps(cert))


def edit_json(bundle, name, f):
    p = bundle / name
    obj = json.loads(p.read_text())
    f(obj)
    p.write_text(json.dumps(obj, separators=(",", ":")))


def flip_label(b):
    edit_json(b, "heldout.json", lambda d: d["rows"][5].__setitem__(-1, (d["rows"][5][-1] + 1) % 10))


def flip_weight(b):
    edit_json(b, "model.json", lambda m: m["codes"].__setitem__(100, (m["codes"][100] + 1) % 4))


# name: (mutation, expected reason substring or None for accept, needs kernel)
CASES = {
    "honest": (lambda b: None, None, True),
    "fake_error_count": (lambda b: edit_json(b, "certificate.json", lambda c: c["claim"].update(errors=10)),
                         "more than the claimed 10", True),
    "fake_tight_bound": (lambda b: edit_json(b, "certificate.json", lambda c: c["claim"]["bound"].update(num=300)),
                         "do not support the bound", True),
    "tampered_data_rehashed": (lambda b: (flip_label(b), rehash(b, ("evidence", "heldout"))),
                               "more than the claimed 16", True),
    "tampered_model_rehashed": (lambda b: (flip_weight(b), rehash(b, ("subject", "model"))),
                                "more than the claimed 16", True),
    "tampered_data": (flip_label, "sha256 mismatch", False),
    "tampered_model": (flip_weight, "sha256 mismatch", False),
    "wrong_toolchain": (lambda b: edit_json(b, "certificate.json",
                        lambda c: c["pins"].update(lean_toolchain="leanprover/lean4:v4.0.0")), "pinned toolchain", False),
    "dropped_assumption": (lambda b: edit_json(b, "certificate.json", lambda c: c.update(assumptions=["A1-iid"])),
                           "omits assumptions", False),
    "unknown_claim_type": (lambda b: edit_json(b, "certificate.json", lambda c: c["claim"].update(type="anything")),
                           "unknown claim type", False),
    "confidence_not_1_over_d": (lambda b: edit_json(b, "certificate.json",
                                lambda c: c["claim"].update(delta={"num": 3, "den": 20})), "claim.delta", False),
    "bound_above_one": (lambda b: edit_json(b, "certificate.json",
                        lambda c: c["claim"]["bound"].update(num=20000)), "num ≤ den", False),
    "path_escape": (lambda b: edit_json(b, "certificate.json",
                    lambda c: c["evidence"]["heldout"].update(path="../honest/heldout.json")), "escapes the bundle", False),
    "row_count_mismatch": (lambda b: edit_json(b, "certificate.json",
                           lambda c: c["evidence"]["heldout"].update(n=1000)), "rows", False),
    "invalid_code": (lambda b: (edit_json(b, "model.json", lambda m: m["codes"].__setitem__(0, 7)),
                                rehash(b, ("subject", "model"))), "codes must be integers in [0, 4)", False),
}


def run(bundle):
    res = subprocess.run([sys.executable, str(OT), "verify", str(bundle), "--json"],
                         capture_output=True, text=True)
    try:
        return json.loads(res.stdout)
    except json.JSONDecodeError:
        return {"accepted": False, "reason": f"verifier crashed: {res.stdout[-500:]}{res.stderr[-500:]}"}


def main():
    fast = "--fast" in sys.argv
    tmp = Path(tempfile.mkdtemp(prefix="ot-conformance-"))
    honest = tmp / "honest"
    subprocess.run([sys.executable, str(OT), "certify", "heldout", str(ARTIFACT), "--out", str(honest)],
                   check=True, capture_output=True)
    selected = {n: c for n, c in CASES.items() if not (fast and c[2])}
    for name, (mutate, _, _) in selected.items():
        if name != "honest":
            shutil.copytree(honest, tmp / name)
            mutate(tmp / name)
    with ThreadPoolExecutor(max_workers=5) as pool:
        results = dict(zip(selected, pool.map(run, [tmp / n for n in selected])))
    failed = 0
    for name, (_, expect, _) in selected.items():
        r = results[name]
        ok = r["accepted"] if expect is None else (not r["accepted"] and expect in r.get("reason", ""))
        failed += not ok
        want = "accept" if expect is None else f"reject ({expect})"
        got = "accepted" if r["accepted"] else f"rejected: {r.get('reason', '')}"
        print(f"[{'ok' if ok else 'FAIL'}] {name}: expected {want}; {got}")
    shutil.rmtree(tmp)
    print(f"\n{len(selected) - failed}/{len(selected)} conformance cases pass")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
