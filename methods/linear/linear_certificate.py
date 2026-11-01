#!/usr/bin/env python3
"""Robustness and monotonicity certificates for linear and logistic-regression models (untrusted).

Writes a certificate bundle for `ot verify` (cards `robust-decision`, `monotone-feature`). The model
file is {"intercept": b, "coef": [w, …]} (scikit-learn's `intercept_[0]`, `coef_[0]`). The
translation and the request are the verifier's own (`verifier/core/linear.py`), so this producer
adds nothing to what is trusted.

    python3 methods/linear/linear_certificate.py robust MODEL BOX --approve|--decline (--tau T | --probability P) --out BUNDLE
    python3 methods/linear/linear_certificate.py monotone MODEL FEATURE --up|--down --out BUNDLE
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("robust")
    r.add_argument("model", type=Path)
    r.add_argument("box", type=Path)
    g = r.add_mutually_exclusive_group(required=True)
    g.add_argument("--approve", action="store_true")
    g.add_argument("--decline", action="store_true")
    t = r.add_mutually_exclusive_group()
    t.add_argument("--tau", help="threshold on the score")
    t.add_argument("--probability", help="threshold on σ(score) (logistic regression)")
    m = sub.add_parser("monotone")
    m.add_argument("model", type=Path)
    m.add_argument("feature", type=int)
    g = m.add_mutually_exclusive_group(required=True)
    g.add_argument("--up", action="store_true")
    g.add_argument("--down", action="store_true")
    for p in (r, m):
        p.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    if a.cmd == "robust":
        claim = {"type": "robust-decision", "version": "0.1", "decision": "approve" if a.approve else "decline",
                 "box": json.loads(a.box.read_text())}
        if a.probability is not None:
            claim["probability"] = a.probability
        else:
            claim["tau"] = a.tau or "0"
    else:
        claim = {"type": "monotone-feature", "version": "0.1", "feature": a.feature,
                 "direction": "increasing" if a.up else "decreasing"}
    a.out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(a.model, a.out / "model.json")
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    cert = {
        "format": "opentheory-certificate/0.1",
        "claim": claim,
        "subject": {"model": {"path": "model.json", "sha256": hashlib.sha256((a.out / "model.json").read_bytes()).hexdigest()}},
        "evidence": {},
        "assumptions": ["A3-model-binding", "A11-model-translation"],
        "pins": {"lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(), "opentheory_commit": commit},
    }
    (a.out / "certificate.json").write_text(json.dumps(cert, indent=2) + "\n")
    print(f"wrote {a.out}/certificate.json; check it with: interfaces/cli/ot verify {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
