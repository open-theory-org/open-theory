#!/usr/bin/env python3
"""Robustness and monotonicity certificates for tree ensembles (untrusted producer).

Writes a certificate bundle for `ot verify` (claim cards `robust-decision`, `monotone-feature`), or the raw
request that `ot_kernel` checks. The translation of the model to integers, the witnesses and the
encoding are the verifier's own (`verifier/core/trees.py`): the verifier recomputes them, so this
producer adds nothing to what is trusted. What an accepted check means is proved once in Lean
(`ClaimTypes.treeRobust`, `ClaimTypes.treeMonotone`).

    python3 methods/trees/tree_certificate.py robust MODEL BOX --approve|--decline [--tau T] --out BUNDLE
    python3 methods/trees/tree_certificate.py monotone MODEL FEATURE --up|--down [--box BOX] --out BUNDLE
      without --out: print the request (one line, for `ot_kernel --stdin`); --check: also run ot_kernel
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
sys.path.insert(0, str(ROOT))
from verifier.core.trees import (NotSupported, monotone_request, plain, reach, robust_request,  # noqa: E402,F401
                                 scale, scale_box, zig, cuts, enc_tree, enc_cuts, enc_box)


def load_model(path: Path) -> dict:
    return plain(json.loads(path.read_text()))


def ot_kernel(cli: str, req: list[int], time: bool = False) -> tuple[bool, str]:
    exe = ROOT / ".lake/build/bin/ot_kernel"
    args = [str(exe), "--stdin"] + (["--time"] if time else [])
    out = subprocess.run(args, input=f"{cli} {' '.join(map(str, req))}\n", capture_output=True, text=True)
    return out.stdout.strip() == "true", out.stderr.strip()


def write_bundle(out: Path, model_path: Path, claim: dict, assumptions: list[str]) -> None:
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(model_path, out / "model.json")
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    cert = {
        "format": "opentheory-certificate/0.1",
        "claim": claim,
        "subject": {"model": {"path": "model.json",
                              "sha256": hashlib.sha256((out / "model.json").read_bytes()).hexdigest()}},
        "evidence": {},
        "assumptions": assumptions,
        "pins": {"lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(), "opentheory_commit": commit},
    }
    (out / "certificate.json").write_text(json.dumps(cert, indent=2) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("robust")
    r.add_argument("model", type=Path)
    r.add_argument("box", type=Path)
    g = r.add_mutually_exclusive_group(required=True)
    g.add_argument("--approve", action="store_true")
    g.add_argument("--decline", action="store_true")
    r.add_argument("--tau", default="0", help="decision threshold on the raw score (logit of the probability cut)")
    m = sub.add_parser("monotone")
    m.add_argument("model", type=Path)
    m.add_argument("feature", type=int)
    g = m.add_mutually_exclusive_group(required=True)
    g.add_argument("--up", action="store_true")
    g.add_argument("--down", action="store_true")
    m.add_argument("--box", type=Path)
    for p in (r, m):
        p.add_argument("--check", action="store_true", help="run ot_kernel on the request")
        p.add_argument("--out", type=Path, help="write a certificate bundle for `ot verify`")
    a = ap.parse_args()
    model = load_model(a.model)
    assumptions = ["A3-model-binding", "A11-tree-translation"]
    if a.cmd == "robust":
        box = json.loads(a.box.read_text())
        claim = {"type": "robust-decision", "version": "0.1", "decision": "approve" if a.approve else "decline",
                 "tau": str(a.tau), "box": box}
        cli, (req, _) = "tree-robust", robust_request(model, box, a.approve, a.tau)
    else:
        box = json.loads(a.box.read_text()) if a.box else {}
        claim = {"type": "monotone-feature", "version": "0.1", "feature": a.feature,
                 "direction": "increasing" if a.up else "decreasing", "box": box}
        res = monotone_request(model, a.feature, a.up, box)
        if res is None:
            print("not certifiable: some tree is not monotone on the box (sufficient condition)", file=sys.stderr)
            return 1
        cli, (req, _) = "tree-monotone", res
    if a.out:
        write_bundle(a.out, a.model, claim, assumptions)
        print(f"wrote {a.out}/certificate.json; check it with: interfaces/cli/ot verify {a.out}")
        return 0
    if a.check:
        ok, log = ot_kernel(cli, req, time=True)
        print(log, file=sys.stderr)
        return 0 if ok else 1
    print(cli, *req)
    return 0


if __name__ == "__main__":
    sys.exit(main())
