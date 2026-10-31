#!/usr/bin/env python3
"""Every citation points to a real entry of blueprint/src/references.bib.

One bibliography for the whole repository, cited by key:

* blueprint: `\\cite{key}` in blueprint/src/content.tex;
* Markdown and Lean docstrings: Pandoc-style `[@key]` (several: `[@a; @b]`);
* catalog manifests: `references = [{ key = "...", relation = "..." }]`, where `relation` says
  how the method relates to the source and `adapts` needs a `note` saying what changed.

Fails on an unknown key or relation. Warns (does not fail) for methods with no references yet.
"""
from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BIB = ROOT / "blueprint" / "src" / "references.bib"
RELATIONS = {"implements", "adapts", "formalizes", "background", "contrasts"}
SCANNED = ["formal", "specs", "catalog", "docs", "research/literature", "methods", "verifier"]


def main() -> int:
    keys = set(re.findall(r"^@\w+\{([^,\s]+),", BIB.read_text(), re.M))
    errors, warnings, uses = [], [], 0

    def need(key: str, where: str) -> None:
        nonlocal uses
        uses += 1
        if key not in keys:
            errors.append(f"{where}: unknown reference '{key}' (add it to {BIB.relative_to(ROOT)})")

    content = (ROOT / "blueprint" / "src" / "content.tex").read_text()
    for group in re.findall(r"\\cite[pt]?\{([^}]*)\}", content):
        for key in group.split(","):
            need(key.strip(), "blueprint/src/content.tex")

    for top in SCANNED:
        for path in sorted((ROOT / top).rglob("*")):
            if path.suffix not in {".md", ".lean"} or "vendors" in path.parts:
                continue
            # inline code spans (`...`) only show the syntax, they are not citations
            text = re.sub(r"`[^`\n]*`", "", path.read_text(encoding="utf-8"))
            for group in re.findall(r"\[(@[^\]]+)\]", text):
                for key in re.findall(r"@([A-Za-z][\w:-]*)", group):
                    need(key, str(path.relative_to(ROOT)))

    for path in sorted((ROOT / "catalog").rglob("*.toml")):
        manifest = tomllib.loads(path.read_text())
        refs = manifest.get("references")
        where = str(path.relative_to(ROOT))
        if refs is None:
            if path.parent.name == "methods":
                warnings.append(f"{where}: no references yet")
            continue
        for ref in refs:
            need(ref.get("key", ""), where)
            if ref.get("relation") not in RELATIONS:
                errors.append(f"{where}: relation must be one of {sorted(RELATIONS)}, got {ref.get('relation')!r}")
            if ref.get("relation") == "adapts" and not ref.get("note"):
                errors.append(f"{where}: 'adapts' needs a note saying what changed ({ref.get('key')})")

    for w in warnings:
        print(f"[WARN] {w}")
    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    print(f"[OK] {uses} citations resolve to {len(keys)} entries of {BIB.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
