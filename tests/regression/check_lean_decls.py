#!/usr/bin/env python3
"""Fail if any \\lean{Name} in the blueprint is missing from formal/core/ and examples/.

This is a lightweight stand-in for `leanblueprint checkdecls` on pull requests.
The Pages workflow still runs the official checkdecls via docgen-action.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CONTENT = ROOT / "blueprint" / "src" / "content.tex"
LEAN_ROOTS = (ROOT / "formal" / "core", ROOT / "examples")

LEAN_MACRO = re.compile(r"\\lean\{([^}]+)\}")
DECL = re.compile(
    r"^\s*(?:(?:protected|noncomputable|scoped|private)\s+)*"
    r"(?:theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+"
    r"([^\s:({\[\n]+)",
    re.MULTILINE,
)


def declared_names() -> set[str]:
    return set(declared_index())


def declared_index() -> dict[str, Path]:
    """Every declared name (and its qualified forms), with the file that declares it."""
    where: dict[str, Path] = {}
    for path in (p for r in LEAN_ROOTS for p in r.rglob("*.lean")):
        names: set[str] = set()
        text = path.read_text(encoding="utf-8")
        # This is only a source index; audit_axioms.lean resolves the references
        # against Lean itself. Track namespaces/sections for qualified local names.
        scopes: list[str] = []
        scope_events = iter(re.finditer(
            r"^\s*(?:noncomputable\s+)?(namespace|section|end)\b(?:[ \t]+([A-Za-z0-9_'.]+))?",
            text, re.MULTILINE,
        ))
        event = next(scope_events, None)
        for match in DECL.finditer(text):
            while event is not None and event.start() < match.start():
                kind, name = event.groups()
                if kind == "end":
                    if scopes:
                        scopes.pop()
                else:
                    scopes.append((name or "") if kind == "namespace" else "")
                event = next(scope_events, None)
            raw = match.group(1)
            prefix = ".".join(scope for scope in scopes if scope)
            names.add(f"{prefix}.{raw}" if prefix else raw)
            short = raw.split(".")[-1]
            names.add(raw)
            names.add(short)
            names.add(f"OpenTheory.{short}")
            if raw.startswith("OpenTheory."):
                names.add(raw)
            else:
                names.add(f"OpenTheory.{raw}")
        for n in names:
            where.setdefault(n, path)
    return where


def blueprint_names() -> list[str]:
    text = CONTENT.read_text(encoding="utf-8")
    found: list[str] = []
    for block in LEAN_MACRO.findall(text):
        for part in block.split(","):
            name = part.strip()
            if name:
                found.append(name)
    return found


def main() -> int:
    if not CONTENT.exists():
        print(f"missing {CONTENT}", file=sys.stderr)
        return 1
    declared = declared_names()
    missing = [name for name in blueprint_names() if name not in declared]
    if missing:
        print("[FATAL] Blueprint \\lean names with no matching declaration:")
        for name in missing:
            print(f"  {name}")
        return 1
    print(f"[OK] All {len(blueprint_names())} \\lean names exist in formal/ and examples/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
