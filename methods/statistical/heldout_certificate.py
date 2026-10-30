#!/usr/bin/env python3
"""Write a `heldout-error` v0.1 certificate bundle for a quantized MLP (untrusted producer).

Computes the held-out error count and the tightest exact binomial bound, then writes
  <out>/model.json, <out>/heldout.json, <out>/certificate.json.
`ot verify <out>` re-checks everything with the Lean kernel; nothing here is trusted.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import binomial_bound  # noqa: E402
from pacbayes_mlp_certificate import error_count  # noqa: E402

ASSUMPTIONS = ["A1-iid", "A2-heldout-independent", "A3-model-binding", "A4-labels"]
ARCH_KEYS = ("inputs", "hidden", "classes", "hidden_bias_scale", "output_bias_scale")


def write_json(path: Path, obj) -> str:
    data = json.dumps(obj, separators=(",", ":")).encode()
    path.write_bytes(data)
    return hashlib.sha256(data).hexdigest()


def certify(model: dict, rows: list, out: Path, scale=10_000, delta_den=20,
            claim_errors: int | None = None, claim_bound: int | None = None, issuer="") -> dict:
    """Write the bundle. `claim_errors` / `claim_bound` (in units of 1/scale) override the honest values."""
    model = {"model_type": "quantized-mlp", **{k: model[k] for k in ARCH_KEYS}, "codes": list(model["codes"])}
    k_true = error_count(model, rows)
    k = k_true if claim_errors is None else claim_errors
    a = binomial_bound.tightest_bound(len(rows), k_true, scale, delta_den) if claim_bound is None else claim_bound
    out.mkdir(parents=True, exist_ok=True)
    model_sha = write_json(out / "model.json", model)
    data_sha = write_json(out / "heldout.json", {"rows": rows})
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    cert = {
        "format": "opentheory-certificate/0.1",
        "claim": {"type": "heldout-error", "version": "0.1", "errors": k,
                  "bound": {"num": a, "den": scale}, "delta": {"num": 1, "den": delta_den}},
        "subject": {"model": {"path": "model.json", "sha256": model_sha}},
        "evidence": {"heldout": {"path": "heldout.json", "sha256": data_sha, "n": len(rows)}},
        "assumptions": ASSUMPTIONS,
        "pins": {"lean_toolchain": toolchain, "opentheory_commit": commit},
        "issuer": issuer,
        "created": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }
    (out / "certificate.json").write_text(json.dumps(cert, indent=2) + "\n")
    return cert


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(prog="ot certify heldout", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("artifact", type=Path, help="JSON with 'model' and 'heldout_rows'")
    ap.add_argument("--out", type=Path, required=True, help="bundle directory to write")
    ap.add_argument("--confidence-den", type=int, default=20, help="δ = 1/d (default 20, i.e. 95%%)")
    ap.add_argument("--issuer", default="")
    args = ap.parse_args(argv)
    art = json.loads(args.artifact.read_text())
    cert = certify(art["model"], [list(r) for r in art["heldout_rows"]], args.out,
                   delta_den=args.confidence_den, issuer=args.issuer)
    c = cert["claim"]
    print(f"wrote {args.out}/: {c['errors']} errors on {cert['evidence']['heldout']['n']} rows, "
          f"bound {c['bound']['num'] / c['bound']['den']:.2%} at {1 - 1 / c['delta']['den']:.0%}")


if __name__ == "__main__":
    main()
