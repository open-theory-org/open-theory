#!/usr/bin/env python3
"""The registries in specs/ are consistent, and specs/coverage.md is generated from them.

Every card (specs/{models,properties,scopes,claims}/*.md) starts with a TOML header between `+++`
lines. A claim is a property × a scope (docs/specs.md); its card links the property, the scope,
the models, the Lean template and the bridge theorem that gives the generic guarantee `Sound`
(`formal/core/Specs/Instances.lean`), the fast checks of `Checks/Registry.lean`, the catalog
methods, the assumptions and the references. This script fails on any broken link, on a claim
that omits an assumption of its scope, and on a stale coverage matrix.

    python3 tests/regression/check_specs.py           # check
    python3 tests/regression/check_specs.py --write   # regenerate specs/coverage.md
"""
from __future__ import annotations

import importlib.util
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPECS = ROOT / "specs"
COVERAGE = SPECS / "coverage.md"
LEVELS = ["experimental", "specified", "verified"]
RELATIONS = {"implements", "adapts", "formalizes", "background", "contrasts"}
FIELDS = {
    "models": {"id", "family", "lean", "references"},
    "properties": {"id", "object", "test", "lean", "references"},
    "scopes": {"id", "kind", "randomness", "assumptions", "lean", "references"},
    "claims": {"id", "property", "scope", "models", "lean", "sound", "checks", "methods",
               "assumptions", "references"},
}
SCOPE_KINDS = {"region", "population"}


def module(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def cards(kind: str) -> dict[str, tuple[Path, dict]]:
    out = {}
    for path in sorted((SPECS / kind).glob("*.md")):
        if path.name == "README.md":
            continue
        text = path.read_text(encoding="utf-8")
        m = re.match(r"\+\+\+\n(.*?)\n\+\+\+\n", text, re.S)
        out[path.stem] = (path, tomllib.loads(m.group(1)) if m else None)
    return out


def main() -> int:
    errors: list[str] = []
    declared = module(ROOT / "tests/regression/check_lean_decls.py").declared_names()
    bib = set(re.findall(r"^@\w+\{([^,\s]+),", (ROOT / "blueprint/src/references.bib").read_text(), re.M))
    assumptions = set(re.findall(r"^## (A\d+-[\w-]+)", (SPECS / "assumptions/README.md").read_text(), re.M))
    registry = set(re.findall(r'cli := "([^"]+)"', (ROOT / "formal/core/Checks/Registry.lean").read_text()))
    methods = {}
    for p in (ROOT / "catalog/methods").glob("*.toml"):
        m = tomllib.loads(p.read_text())
        methods[m["id"]] = m

    reg = {kind: cards(kind) for kind in FIELDS}
    for kind, entries in reg.items():
        for cid, (path, card) in entries.items():
            where = str(path.relative_to(ROOT))
            if card is None:
                errors.append(f"{where}: no `+++` TOML header")
                continue
            missing = FIELDS[kind] - card.keys()
            if missing:
                errors.append(f"{where}: missing fields {sorted(missing)}")
            if card.get("id") != cid:
                errors.append(f"{where}: id {card.get('id')!r} must match the file name {cid!r}")
            for name in card.get("lean", []) + card.get("sound", []):
                if name not in declared:
                    errors.append(f"{where}: unknown Lean declaration {name}")
            for ref in card.get("references", []):
                if ref.get("key") not in bib:
                    errors.append(f"{where}: unknown reference {ref.get('key')!r}")
                if ref.get("relation") not in RELATIONS:
                    errors.append(f"{where}: relation must be one of {sorted(RELATIONS)}")
                if ref.get("relation") == "adapts" and not ref.get("note"):
                    errors.append(f"{where}: 'adapts' needs a note saying what changed")
            for a in card.get("assumptions", []):
                if a not in assumptions:
                    errors.append(f"{where}: unknown assumption {a} (see specs/assumptions/README.md)")
            if kind == "scopes" and card.get("kind") not in SCOPE_KINDS:
                errors.append(f"{where}: kind must be one of {sorted(SCOPE_KINDS)}")

    for cid, (path, c) in reg["claims"].items():
        if c is None:
            continue
        where = str(path.relative_to(ROOT))
        if c.get("property") not in reg["properties"]:
            errors.append(f"{where}: unknown property {c.get('property')!r}")
        scope = reg["scopes"].get(c.get("scope"), (None, None))[1]
        if scope is None:
            errors.append(f"{where}: unknown scope {c.get('scope')!r}")
        else:
            for a in sorted(set(scope.get("assumptions", [])) - set(c.get("assumptions", []))):
                errors.append(f"{where}: omits assumption {a} of its scope {c['scope']}")
        for m in c.get("models", []):
            if m not in reg["models"]:
                errors.append(f"{where}: unknown model {m!r}")
        for chk in c.get("checks", []):
            if chk not in registry:
                errors.append(f"{where}: check {chk!r} is not in formal/core/Checks/Registry.lean")
        for m in c.get("methods", []):
            if m not in methods:
                errors.append(f"{where}: unknown catalog method {m!r}")
    for p in (ROOT / "catalog/guarantees").glob("*.toml"):
        g = tomllib.loads(p.read_text())
        if g.get("claim") not in reg["claims"]:
            errors.append(f"{p.relative_to(ROOT)}: claim {g.get('claim')!r} has no card in specs/claims/")

    fresh = coverage(reg, methods)
    if "--write" in sys.argv:
        COVERAGE.write_text(fresh, encoding="utf-8")
    elif not COVERAGE.exists() or COVERAGE.read_text(encoding="utf-8") != fresh:
        errors.append("specs/coverage.md is stale: run tests/regression/check_specs.py --write")

    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    counts = {k: len(v) for k, v in reg.items()}
    print(f"[OK] specs registries consistent: {counts}")
    return 0


def status(claim: dict, methods: dict) -> str:
    """Best level among the claim's methods; otherwise how far its Lean side goes."""
    levels = [methods[m]["level"] for m in claim.get("methods", []) if m in methods]
    if levels:
        best = max(levels, key=LEVELS.index)
        return f"**{best}**" + ("" if claim.get("sound") else ", no `Sound` bridge yet")
    return "theorem" if claim.get("sound") else "statement"


def coverage(reg: dict, methods: dict) -> str:
    claims = [c for _, c in reg["claims"].values() if c]
    rows: dict[tuple[str, str], dict[str, list[str]]] = {}
    for c in claims:
        kind = reg["scopes"][c["scope"]][1]["kind"] if c["scope"] in reg["scopes"] else "?"
        for m in c["models"]:
            rows.setdefault((m, c["property"]), {}).setdefault(kind, []).append(
                f"[`{c['id']}`](claims/{c['id']}.md) ({status(c, methods)})")
    lines = [
        "# Coverage",
        "",
        "Generated by `tests/regression/check_specs.py --write` from the cards in `specs/` and the",
        "levels in `catalog/`. Do not edit by hand. A claim is a property × a scope (`docs/specs.md`).",
        "",
        "| Model | Property | Region | Population |",
        "| --- | --- | --- | --- |",
    ]
    for (m, p), cells in sorted(rows.items()):
        lines.append(f"| [{m}](models/{m}.md) | [{p}](properties/{p}.md) | "
                     f"{'<br>'.join(cells.get('region', [])) or '—'} | "
                     f"{'<br>'.join(cells.get('population', [])) or '—'} |")
    lines += [
        "",
        "Status: the best level of the claim's catalog methods; `theorem`: the bridge to the generic",
        "guarantee `Sound` is proved but no method uses it yet; `statement`: the template exists only.",
        "",
        "| Claim | Property | Scope | Guarantee (`formal/core/Specs/Instances.lean`) | Fast checks | Methods | Assumptions |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for c in sorted(claims, key=lambda c: c["id"]):
        lines.append(
            f"| [`{c['id']}`](claims/{c['id']}.md) | {c['property']} | {c['scope']} | "
            f"{', '.join('`' + s.rsplit('.', 1)[-1] + '`' for s in c['sound']) or 'open'} | "
            f"{', '.join('`' + x + '`' for x in c['checks']) or '—'} | "
            f"{', '.join(c['methods']) or '—'} | {', '.join(c['assumptions']) or '—'} |")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
