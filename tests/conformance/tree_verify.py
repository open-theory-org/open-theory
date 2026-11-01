#!/usr/bin/env python3
"""Conformance of `ot verify` on `tree-robust` and `tree-monotone` bundles.

Writes bundles for the LightGBM example (`examples/tree_ensemble/`) with the producer and checks
them with the verifier (`verifier.core.engine.verify`):

* accepted: the applicant's approval on the box; monotonicity up in income, down in debt;
  each report's result line says `verified · kernel lane · δ = 0 · assumes A3, A11`;
* rejected: the decline on the same box (false); monotonicity up in debt (false); a model file
  changed after its digest was taken; a digest that does not match; a categorical split; a
  certificate that omits an assumption;
* compiled lane: accepted, labelled "compiled check, not verified".

Requires `lake build ot_kernel ot_check`.
"""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from verifier.core.engine import verify  # noqa: E402

EX = ROOT / "examples" / "tree_ensemble"
PRODUCER = ROOT / "methods" / "trees" / "tree_certificate.py"


def produce(out: Path, *args: str) -> None:
    subprocess.run([sys.executable, str(PRODUCER), *args, "--out", str(out)], check=True, capture_output=True)


def edit(bundle: Path, f) -> None:
    p = bundle / "certificate.json"
    cert = json.loads(p.read_text())
    f(cert, bundle)
    p.write_text(json.dumps(cert, indent=2))


def main() -> int:
    failures, cases = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        model, box = str(EX / "model_lightgbm.json"), str(EX / "box_applicant.json")
        produce(tmp / "approve", "robust", model, box, "--approve")
        produce(tmp / "decline", "robust", model, box, "--decline")
        produce(tmp / "income", "monotone", model, "0", "--up")
        produce(tmp / "debt", "monotone", model, "1", "--down")
        produce(tmp / "debt_up", "monotone", model, "1", "--down")
        schema = json.loads((ROOT / "specs/certificates/schema.json").read_text())
        for b in ("approve", "income"):
            cert = json.loads((tmp / b / "certificate.json").read_text())
            cases += 1
            if missing := [k for k in schema["required"] if k not in cert]:
                failures.append(f"{b}: certificate lacks schema fields {missing}")
            if cert["claim"]["type"] not in schema["properties"]["claim"]["properties"]["type"]["enum"]:
                failures.append(f"{b}: claim type not in the schema")
        edit(tmp / "debt_up", lambda c, b: c["claim"].update(direction="increasing"))

        for name in ("tampered_model", "bad_digest", "categorical", "no_a11"):
            shutil.copytree(tmp / "approve", tmp / name)
        p = tmp / "tampered_model" / "model.json"
        m = json.loads(p.read_text())
        m["tree_info"][2]["tree_structure"]["left_child"]["leaf_value"] = 0.9
        p.write_text(json.dumps(m))
        edit(tmp / "bad_digest", lambda c, b: c["subject"]["model"].update(sha256="0" * 64))

        def categorical(c, b):
            p = b / "model.json"
            m = json.loads(p.read_text())
            m["tree_info"][0]["tree_structure"]["decision_type"] = "=="
            p.write_text(json.dumps(m))
            import hashlib
            c["subject"]["model"]["sha256"] = hashlib.sha256(p.read_bytes()).hexdigest()
        edit(tmp / "categorical", categorical)
        edit(tmp / "no_a11", lambda c, b: c.update(assumptions=["A3-model-binding"]))

        expect = {"approve": True, "income": True, "debt": True, "decline": False, "debt_up": False,
                  "tampered_model": False, "bad_digest": False, "categorical": False, "no_a11": False}
        for name, want in expect.items():
            cases += 1
            r = verify(tmp / name, timeout=120)
            if r.accepted != want:
                failures.append(f"{name}: expected {'accept' if want else 'reject'}, got "
                                f"{'accept' if r.accepted else 'reject'} ({r.reason})")
            elif want and not r.summary().endswith("verified · kernel lane · δ = 0 · assumes A3-model-binding, A11-model-translation"):
                failures.append(f"{name}: result line is {r.summary()!r}")
        cases += 1
        r = verify(tmp / "approve", timeout=120, compiled=True)
        if not r.accepted or "compiled check, not verified" not in r.level or "compiled (not verified) lane" not in r.summary():
            failures.append(f"compiled lane: accepted={r.accepted}, level={r.level!r}, line={r.summary()!r}")

    for f in failures:
        print(f"[FAIL] {f}")
    if failures:
        return 1
    print(f"{cases}/{cases} tree-verify cases pass (bundles through ot verify, both lanes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
