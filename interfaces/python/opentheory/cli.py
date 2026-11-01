"""Implementation of the `ot` command (interfaces/cli/ot)."""
from __future__ import annotations

import argparse
import json
import sys

from . import ROOT, verify


def print_report(r) -> None:
    mark = "ACCEPTED" if r.accepted else "REJECTED"
    print(f"{mark}  {r.claim_type or '?'}  ({r.seconds:.0f}s)")
    print(f"  {r.summary()}")
    if not r.accepted:
        print(f"  reason: {r.reason}")
        return
    print(f"\n  Claim:  {r.claim}")
    print(f"  Level:  {r.level}  (guarantee {r.guarantee}; levels: specs/protocols/assurance-levels.md)")
    print("\n  Checked:")
    for c in r.checked:
        print(f"    - {c}")
    print("\n  Assumed (not checkable from the certificate):")
    for i, s in r.assumptions:
        print(f"    - {i}: {s}")
    print("\n  Trusted:")
    for t in r.trusted:
        print(f"    - {t}")
    print("\n  Does not cover:")
    for d in r.does_not_cover:
        print(f"    - {d}")
    for w in r.warnings:
        print(f"\n  warning: {w}")


def run(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="ot", description="OpenTheory: verifiable claims about AI systems")
    sub = ap.add_subparsers(dest="cmd", required=True)
    v = sub.add_parser("verify", help="check a certificate bundle")
    v.add_argument("bundle", help="directory containing certificate.json")
    v.add_argument("--json", action="store_true", help="print the report as JSON")
    v.add_argument("--timeout", type=int, default=1800, help="Lean kernel time limit in seconds")
    v.add_argument("--compiled", action="store_true",
                   help="run the decision procedure as compiled code (faster; trusts the Lean compiler, "
                        "so the result is not labelled verified)")
    c = sub.add_parser("certify", help="produce a certificate (untrusted)")
    c.add_argument("claim_type", choices=["heldout", "pool-rate"])
    c.add_argument("rest", nargs=argparse.REMAINDER)
    args = ap.parse_args(argv)

    if args.cmd == "certify":
        # Producers are untrusted and only ever loaded for `certify`, never by `verify`.
        sys.path.append(str(ROOT / "methods" / "statistical"))
        if args.claim_type == "pool-rate":
            from pool_rate_certificate import main as certify_main
        else:
            from heldout_certificate import main as certify_main
        certify_main(args.rest)
        return 0
    r = verify(args.bundle, timeout=args.timeout, compiled=args.compiled)
    if args.json:
        print(json.dumps(r.to_dict(), indent=2, ensure_ascii=False))
    else:
        print_report(r)
    return 0 if r.accepted else 1


def main(argv: list[str]) -> int:
    """Exit codes: 0 accepted, 1 rejected, 2 the verifier could not run (never a verdict)."""
    try:
        return run(argv)
    except SystemExit as e:  # argparse usage errors
        return 2 if e.code not in (0, None) else 0
    except KeyboardInterrupt:
        return 130
    except Exception as e:  # noqa: BLE001
        print(f"error: the verifier could not run ({type(e).__name__}: {e}). This is not a verdict.",
              file=sys.stderr)
        return 2
