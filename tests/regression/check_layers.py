#!/usr/bin/env python3
"""Enforce the bottom-up layering of formal/core (see formal/README.md).

A module in layer L may import only modules of L and of the layers before it:
Checks → Foundations → Models → Properties → Theory → Scopes → Specs.

`Checks` holds the executable certificate checks. They must run in a kernel environment with
nothing but Lean's core, so they may import only `Init`, `Std` and other `Checks` modules.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "formal" / "core"
ORDER = ["Checks", "Foundations", "Models", "Properties", "Theory", "Scopes", "Specs"]
CORE_ONLY = ("Init", "Std")


def main() -> int:
    errors = []
    for path in sorted(CORE.rglob("*.lean")):
        layer = path.relative_to(CORE).parts[0]
        if layer not in ORDER:
            errors.append(f"{path.relative_to(ROOT)}: not in a known layer {ORDER}")
            continue
        for target in re.findall(r"^import (\w+)", path.read_text(), re.M):
            if layer == "Checks" and target not in CORE_ONLY and target != "Checks":
                errors.append(f"{path.relative_to(ROOT)}: Checks imports {target} (core Lean only)")
            if target in ORDER and ORDER.index(target) > ORDER.index(layer):
                errors.append(f"{path.relative_to(ROOT)}: {layer} imports later layer {target}")
    for e in errors:
        print(f"[ERROR] {e}")
    if errors:
        return 1
    print(f"[OK] formal/core respects {' → '.join(ORDER)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
