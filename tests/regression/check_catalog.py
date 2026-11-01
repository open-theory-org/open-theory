#!/usr/bin/env python3
"""Enforce the assurance levels of specs/protocols/assurance-levels.md on catalog/.

Each method either establishes claims (`establishes`, cards in specs/claims/) or computes an input
of other methods (`feeds`). Its level is derived from these links (`registry.derive`) and the
declared level must equal it: a method is verified exactly when the kernel checks a chain from its
evidence to the `Sound` theorem of a claim. Each guarantee names one claim and the methods it uses;
its level is that of its weakest method. This script also checks that every Lean name exists, that
every file in methods/ has a manifest, and generates the tables in catalog/README.md, including
"what proves what". Sorry-freedom and axioms are enforced by verifier/backends/formal/audit_axioms.lean.

  python3 tests/regression/check_catalog.py            # check
  python3 tests/regression/check_catalog.py --write    # also regenerate the tables in catalog/README.md
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_decls import declared_names  # noqa: E402
from registry import LEVELS, ROOT, cards, catalog, derive, establishing, feeders, registry_checks  # noqa: E402

METHOD_KEYS = {"id", "name", "level", "kind", "summary", "implementation", "assumptions", "trusted", "conformance"}
METHOD_OPTIONAL = {"mode", "establishes", "feeds", "checks", "not_verified_because", "references", "lean"}
LEAN_KEYS = {"spec", "check", "correctness"}
GUARANTEE_KEYS = {"id", "name", "level", "claim", "uses", "assumptions"}
GUARANTEE_OPTIONAL = {"example"}
TABLE_START, TABLE_END = "<!-- catalog:start -->", "<!-- catalog:end -->"


def assumption_ids():
    return set(re.findall(r"^## (A\d+-[\w-]+)", (ROOT / "specs/assumptions/README.md").read_text(), re.M))


def short(names):
    return ", ".join(f"`{n.rsplit('.', 1)[-1]}`" for n in names) or "—"


def check():
    errors = []
    names = declared_names()
    assumptions = assumption_ids()
    fast = registry_checks()
    methods, guarantees = catalog("methods"), catalog("guarantees")
    claims = {k: v for k, v in cards("claims").items() if v[1] is not None}

    def err(path, msg):
        errors.append(f"{path.relative_to(ROOT)}: {msg}")

    def common(path, m, keys, optional):
        for k in sorted(keys - m.keys()):
            err(path, f"missing field '{k}'")
        for k in sorted(m.keys() - keys - optional):
            err(path, f"unknown field '{k}'")
        if m.get("id") != path.stem:
            err(path, f"id '{m.get('id')}' must equal the file name")
        if m.get("level") not in LEVELS:
            err(path, f"level must be one of {LEVELS}")
        for a in m.get("assumptions", []):
            if a not in assumptions:
                err(path, f"unknown assumption '{a}' (see specs/assumptions/README.md)")

    covered = set()
    for mid, (path, m) in methods.items():
        common(path, m, METHOD_KEYS, METHOD_OPTIONAL)
        lean = m.get("lean", {})
        for k in sorted(lean.keys() - LEAN_KEYS):
            err(path, f"unknown field 'lean.{k}' (one of {sorted(LEAN_KEYS)})")
        for n in [n for k in LEAN_KEYS for n in lean.get(k, [])]:
            if n not in names:
                err(path, f"Lean declaration not found: {n}")
        for f in m.get("implementation", []) + m.get("conformance", []):
            if not (ROOT / f).exists():
                err(path, f"path does not exist: {f}")
        covered |= {(ROOT / f).resolve() for f in m.get("implementation", [])}
        if m.get("kind") and not (ROOT / "methods" / m["kind"]).is_dir():
            err(path, f"kind '{m['kind']}' has no methods/{m['kind']}/ folder")
        for c in m.get("establishes", []):
            if c not in claims:
                err(path, f"establishes unknown claim '{c}' (no card in specs/claims/)")
            else:
                # the `Sound` theorem belongs to the claim; the method proves its premise
                for s in set(claims[c][1].get("sound", [])) & set(lean.get("correctness", [])):
                    err(path, f"{s} is the Sound theorem of claim '{c}': list it on the claim card only")
        for f in m.get("feeds", []):
            if f not in methods:
                err(path, f"feeds unknown method '{f}'")
        for chk in m.get("checks", []):
            if chk not in fast:
                err(path, f"check '{chk}' is not in formal/core/Checks/Registry.lean")
        level, missing = derive(m, claims)
        if m.get("level") != level:
            why = f" (missing: {'; '.join(missing)})" if missing and level != "verified" else ""
            err(path, f"declared level '{m.get('level')}' but the evidence supports '{level}'{why}")

    for gid, (path, g) in guarantees.items():
        common(path, g, GUARANTEE_KEYS, GUARANTEE_OPTIONAL)
        claim = claims.get(g.get("claim"), (None, None))[1]
        if claim is None:
            err(path, f"claim '{g.get('claim')}' has no card in specs/claims/")
        uses = [u for u in g.get("uses", []) if u in methods]
        for u in sorted(set(g.get("uses", [])) - set(uses)):
            err(path, f"unknown method '{u}'")
        if not any(g.get("claim") in methods[u][1].get("establishes", []) for u in uses):
            err(path, f"no method in 'uses' establishes claim '{g.get('claim')}'")
        if uses:
            floor = LEVELS[min(LEVELS.index(methods[u][1]["level"]) for u in uses)]
            if g.get("level") != floor:
                err(path, f"level '{g.get('level')}' must be that of its weakest method ('{floor}')")
        needed = {a for u in uses for a in methods[u][1].get("assumptions", [])}
        needed |= set(claim.get("assumptions", [])) if claim else set()
        for a in sorted(needed - set(g.get("assumptions", []))):
            err(path, f"assumption '{a}' of its claim or of a used method is not declared")
        if g.get("example") and not (ROOT / g["example"]).exists():
            err(path, f"path does not exist: {g['example']}")

    for f in sorted((ROOT / "methods").rglob("*")):
        if f.suffix in {".py", ".lean", ".ts", ".rs"} and f.resolve() not in covered:
            errors.append(f"{f.relative_to(ROOT)}: not covered by any catalog/methods manifest (every method needs a level)")
    return errors, methods, guarantees, claims


def spec_of(c):
    dom = " × ".join(c["domain"]) if isinstance(c["domain"], list) else c["domain"]
    return f"{c['observable']} × {dom} × {c['aggregate']}"


def tables(methods, guarantees, claims):
    rows = [
        "### What proves what",
        "",
        "One row per claim and certifying method. The chain is read right to left: the kernel evaluates",
        "the check on the certificate; the correctness theorems turn an accepting check into the",
        "acceptance condition of the claim's `Sound` theorem, proved once for its specification.",
        "",
        "| Claim | Spec (observable × domain × aggregate) | `Sound`, proved once | Method | Kernel evaluates | Correctness: check ⇒ acceptance | Inputs from | Fast checks | Level |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for cid, (_, c) in sorted(claims.items()):
        est = establishing(cid, methods) or [None]
        for mid in est:
            m = methods[mid][1] if mid else {}
            lean = m.get("lean", {})
            inputs = ", ".join(f"[{f}](methods/{f}.toml)" for f in feeders(mid, methods)) if mid else ""
            method = f"[{mid}](methods/{mid}.toml)" if mid else "—"
            level = f"**{m['level']}**" if mid else ("theorem" if c.get("sound") else "statement")
            rows.append(
                f"| [`{cid}`](../specs/claims/{cid}.md) | {spec_of(c)} | {short(c.get('sound', []))} | {method} | "
                f"{short(lean.get('check', []))} | {short(lean.get('correctness', []))} | {inputs or '—'} | "
                f"{', '.join(f'`{x}`' for x in m.get('checks', [])) or '—'} | {level} |")
    rows += [
        "",
        "### Methods",
        "",
        "| Level | Method | Mode | Role | Kind |",
        "| --- | --- | --- | --- | --- |",
    ]
    order = sorted(methods.items(), key=lambda kv: (-LEVELS.index(kv[1][1]["level"]), kv[0]))
    for mid, (path, m) in order:
        role = ([f"establishes {', '.join(m['establishes'])}"] if m.get("establishes") else []) + \
               ([f"feeds {', '.join(m['feeds'])}"] if m.get("feeds") else [])
        rows.append(f"| **{m['level']}** | [{m['name']}](methods/{path.name}) | {m.get('mode', '-')} | "
                    f"{'; '.join(role) or 'research'} | {m['kind']} |")
    rows += ["", "### Guarantees", "", "| Level | Guarantee | Claim | Uses | Assumptions |", "| --- | --- | --- | --- | --- |"]
    for gid, (path, g) in guarantees.items():
        rows.append(f"| **{g['level']}** | [{g['name']}](guarantees/{path.name}) | `{g['claim']}` | "
                    f"{', '.join(g['uses'])} | {', '.join(g['assumptions'])} |")
    return "\n".join(rows)


def main():
    errors, methods, guarantees, claims = check()
    readme = ROOT / "catalog/README.md"
    text = readme.read_text(encoding="utf-8")
    start, end = text.index(TABLE_START) + len(TABLE_START), text.index(TABLE_END)
    fresh = text[:start] + "\n" + tables(methods, guarantees, claims) + "\n" + text[end:]
    if "--write" in sys.argv:
        readme.write_text(fresh, encoding="utf-8")
    elif fresh != text:
        errors.append("catalog/README.md tables are stale: run tests/regression/check_catalog.py --write")
    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    counts = {lvl: sum(m["level"] == lvl for _, m in methods.values()) for lvl in reversed(LEVELS)}
    print(f"[OK] {len(methods)} methods ({counts}), {len(guarantees)} guarantees; levels derived from the links")
    return 0


if __name__ == "__main__":
    sys.exit(main())
