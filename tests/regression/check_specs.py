#!/usr/bin/env python3
"""The registries in specs/ are consistent, and specs/coverage.md is generated from them.

Every card (specs/{models,properties,domains,claims}/*.md) starts with a TOML header between `+++`
lines. A claim card is a claim type: an observable (a property or a quantity) × a domain × an
aggregate (docs/language.md); it links them, the models, its claim types in Lean
(`formal/core/Specs/ClaimTypes.lean`, each with its `Sound` theorem), the assumptions and the
references. Which methods establish a claim, and its fast checks, are read from catalog/ (each
method's `establishes` and `checks`), never written on the card. This script fails
on any broken link, on an aggregate its domain cannot carry, on a claim that omits an assumption of
its domain, and on a stale coverage matrix.

    python3 tests/regression/check_specs.py           # check
    python3 tests/regression/check_specs.py --write   # regenerate specs/coverage.md
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from registry import LEVELS, ROOT, SPECS, cards, catalog, establishing  # noqa: E402

COVERAGE = SPECS / "coverage.md"
RELATIONS = {"implements", "adapts", "formalizes", "background", "contrasts"}
FIELDS = {
    "models": {"id", "family", "type", "lean", "references"},
    "properties": {"id", "kind", "object", "test", "lean", "references"},
    "domains": {"id", "kind", "randomness", "assumptions", "lean", "references"},
    "claims": {"id", "observable", "domain", "aggregate", "models", "lean", "claim_types", "assumptions",
               "references"},
}
OBSERVABLE_KINDS = {"property", "quantity"}
# the Lean object of a claim type an assumption ties to the world (specs/assumptions/README.md)
BRIDGES = {"law", "observable", "domain", "model"}
DOMAIN_KINDS = ["region", "pool", "distribution", "pair"]
# `OpenTheory.Aggregate`, and the domain kinds each one has a meaning on (`Spec.Target`)
AGGREGATES = {
    "all": {"region", "pool", "distribution", "pair"},
    "meanLe": {"pool", "distribution"},
    "meanGe": {"pool", "distribution"},
    "quantileLe": {"pool", "distribution"},
    "gapLe": {"pair"},
    "ratioGe": {"pair"},
}


def module(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    errors: list[str] = []
    declared = module(ROOT / "tests/regression/check_lean_decls.py").declared_names()
    bib = set(re.findall(r"^@\w+\{([^,\s]+),", (ROOT / "blueprint/src/references.bib").read_text(), re.M))
    atext = (SPECS / "assumptions/README.md").read_text()
    assumptions = set(re.findall(r"^## (A\d+-[\w-]+)", atext, re.M))
    for aid, kind in re.findall(r"^## (A\d+-[\w-]+):.*\n\n(?:\*\*Bridges:\*\* (\w+))?", atext, re.M):
        if kind not in BRIDGES:
            errors.append(f"specs/assumptions/README.md: {aid} needs a `**Bridges:**` line, one of {sorted(BRIDGES)}")
    methods = {mid: m for mid, (_, m) in catalog("methods").items()}

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
            for name in card.get("lean", []) + card.get("claim_types", []):
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
            if kind == "domains" and card.get("kind") not in DOMAIN_KINDS:
                errors.append(f"{where}: kind must be one of {DOMAIN_KINDS}")
            if kind == "properties" and card.get("kind") not in OBSERVABLE_KINDS:
                errors.append(f"{where}: kind must be one of {sorted(OBSERVABLE_KINDS)}")

    for cid, (path, c) in reg["claims"].items():
        if c is None:
            continue
        where = str(path.relative_to(ROOT))
        if c.get("observable") not in reg["properties"]:
            errors.append(f"{where}: unknown observable {c.get('observable')!r}")
        # a domain is one card, or a pair of two cards
        names = c.get("domain") if isinstance(c.get("domain"), list) else [c.get("domain")]
        doms = [reg["domains"].get(n, (None, None))[1] for n in names]
        if len(names) not in (1, 2) or None in doms:
            errors.append(f"{where}: domain must be one or two domain cards, got {c.get('domain')!r}")
        else:
            kind = "pair" if len(doms) == 2 else doms[0]["kind"]
            agg = c.get("aggregate")
            if agg not in AGGREGATES:
                errors.append(f"{where}: aggregate must be one of {sorted(AGGREGATES)}")
            elif kind not in AGGREGATES[agg]:
                errors.append(f"{where}: aggregate {agg} has no meaning on a {kind} domain")
            needed = {a for d in doms for a in d.get("assumptions", [])}
            for a in sorted(needed - set(c.get("assumptions", []))):
                errors.append(f"{where}: omits assumption {a} of its domain")
        for m in c.get("models", []):
            if m not in reg["models"]:
                errors.append(f"{where}: unknown model {m!r}")
        for k in ("methods", "checks"):
            if k in c:
                errors.append(f"{where}: '{k}' is derived from catalog/methods (`establishes`, `checks`); remove it")
        for mid in establishing(cid, {k: (None, v) for k, v in methods.items()}):
            for a in sorted(set(methods[mid].get("assumptions", [])) - set(c.get("assumptions", []))):
                errors.append(f"{where}: omits assumption {a} of its method {mid}")

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


def claim_methods(claim: dict, methods: dict) -> list[str]:
    return establishing(claim["id"], {k: (None, v) for k, v in methods.items()})


def status(claim: dict, methods: dict) -> str:
    """Best level among the methods establishing the claim; otherwise how far its Lean side goes."""
    levels = [methods[m]["level"] for m in claim_methods(claim, methods)]
    if levels:
        best = max(levels, key=LEVELS.index)
        return f"**{best}**" + ("" if claim.get("claim_types") else ", no claim type yet")
    return "theorem" if claim.get("claim_types") else "statement"


def domain_kind(c: dict, reg: dict) -> str:
    if isinstance(c["domain"], list):
        return "pair"
    return reg["domains"][c["domain"]][1]["kind"] if c["domain"] in reg["domains"] else "?"


def coverage(reg: dict, methods: dict) -> str:
    claims = [c for _, c in reg["claims"].values() if c]
    rows: dict[tuple[str, str], dict[str, list[str]]] = {}
    for c in claims:
        for m in c["models"]:
            rows.setdefault((m, c["observable"]), {}).setdefault(domain_kind(c, reg), []).append(
                f"[`{c['id']}`](claims/{c['id']}.md) {c['aggregate']} ({status(c, methods)})")
    lines = [
        "# Coverage",
        "",
        "Generated by `tests/regression/check_specs.py --write` from the cards in `specs/` and the",
        "levels in `catalog/`. Do not edit by hand. A claim is an observable × a domain × an aggregate",
        "(`docs/specs.md`).",
        "",
        "| Model | Observable | " + " | ".join(k.capitalize() for k in DOMAIN_KINDS) + " |",
        "| --- | --- | " + " | ".join("---" for _ in DOMAIN_KINDS) + " |",
    ]
    for (m, p), cells in sorted(rows.items()):
        lines.append(f"| [{m}](models/{m}.md) | [{p}](properties/{p}.md) | "
                     + " | ".join("<br>".join(cells.get(k, [])) or "—" for k in DOMAIN_KINDS) + " |")
    lines += [
        "",
        "Status: the best level of the catalog methods establishing the claim; `theorem`: a claim type with",
        "its `Sound` theorem exists but no method uses it yet; `statement`: the card exists only.",
        "",
        "| Claim | Observable | Domain | Aggregate | Claim types (`formal/core/Specs/ClaimTypes.lean`) | Fast checks | Methods | Assumptions |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for c in sorted(claims, key=lambda c: c["id"]):
        dom = " × ".join(c["domain"]) if isinstance(c["domain"], list) else c["domain"]
        ms = claim_methods(c, methods)
        checks = sorted({x for m in ms for x in methods[m].get("checks", [])})
        lines.append(
            f"| [`{c['id']}`](claims/{c['id']}.md) | {c['observable']} | {dom} | {c['aggregate']} | "
            f"{', '.join('`' + s.rsplit('.', 1)[-1] + '`' for s in c['claim_types']) or 'open'} | "
            f"{', '.join('`' + x + '`' for x in checks) or '—'} | "
            f"{', '.join(ms) or '—'} | {', '.join(c['assumptions']) or '—'} |")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
