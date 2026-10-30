#!/usr/bin/env python3
"""Enforce the assurance levels of specs/protocols/assurance-levels.md on catalog/.

Checks every manifest's fields, that its Lean references exist, that every file in
methods/ is covered by a manifest, and that no guarantee claims more than its methods.
Sorry-freedom and axioms are enforced separately by verifier/backends/formal/audit_axioms.lean,
which audits every OpenTheory declaration.

  python3 tests/regression/check_catalog.py            # check
  python3 tests/regression/check_catalog.py --write    # also regenerate the table in catalog/README.md
"""
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_decls import declared_names  # noqa: E402

LEVELS = ["experimental", "specified", "verified"]
MODES = {"verified-implementation", "verified-checker"}
METHOD_KEYS = {"id", "name", "level", "kind", "summary", "implementation", "assumptions", "trusted", "conformance"}
GUARANTEE_KEYS = {"id", "name", "level", "claim", "uses", "assumptions"}
TABLE_START, TABLE_END = "<!-- catalog:start -->", "<!-- catalog:end -->"


def load(kind):
    return {p: tomllib.loads(p.read_text(encoding="utf-8")) for p in sorted((ROOT / "catalog" / kind).glob("*.toml"))}


def assumption_ids():
    return set(re.findall(r"^## (A\d+-[\w-]+)", (ROOT / "specs/assumptions/README.md").read_text(), re.M))


def check():
    errors = []
    names = declared_names()
    assumptions = assumption_ids()
    methods, guarantees = load("methods"), load("guarantees")

    def err(path, msg):
        errors.append(f"{path.relative_to(ROOT)}: {msg}")

    def check_lean(path, refs):
        for n in refs:
            if n not in names:
                err(path, f"Lean declaration not found: {n}")

    def check_common(path, m, keys):
        for k in sorted(keys - m.keys()):
            err(path, f"missing field '{k}'")
        if m.get("id") != path.stem:
            err(path, f"id '{m.get('id')}' must equal the file name")
        if m.get("level") not in LEVELS:
            err(path, f"level must be one of {LEVELS}")
        for a in m.get("assumptions", []):
            if a not in assumptions:
                err(path, f"unknown assumption '{a}' (see specs/assumptions/README.md)")

    covered = set()
    by_id = {}
    for path, m in methods.items():
        check_common(path, m, METHOD_KEYS)
        by_id[m.get("id")] = m
        lean = m.get("lean", {})
        for f in m.get("implementation", []) + m.get("conformance", []):
            if not (ROOT / f).exists():
                err(path, f"path does not exist: {f}")
        covered |= {(ROOT / f).resolve() for f in m.get("implementation", [])}
        if m.get("kind") and not (ROOT / "methods" / m["kind"]).is_dir():
            err(path, f"kind '{m['kind']}' has no methods/{m['kind']}/ folder")
        level = m.get("level")
        if level == "verified":
            if m.get("mode") not in MODES:
                err(path, f"verified methods need mode in {sorted(MODES)}")
            if not lean.get("spec") or not lean.get("correctness"):
                err(path, "verified methods need lean.spec and lean.correctness")
            if not m.get("conformance"):
                err(path, "verified methods need at least one conformance test")
        elif level == "specified":
            if not lean.get("spec"):
                err(path, "specified methods need lean.spec")
            if not m.get("not_verified_because"):
                err(path, "specified methods must say why they are not verified (not_verified_because)")
        elif level == "experimental" and lean.get("correctness"):
            err(path, "an experimental method with a correctness theorem should be specified or verified")
        check_lean(path, lean.get("spec", []) + lean.get("correctness", []))

    for path, g in guarantees.items():
        check_common(path, g, GUARANTEE_KEYS)
        uses = [by_id.get(u) for u in g.get("uses", [])]
        for u, m in zip(g.get("uses", []), uses):
            if m is None:
                err(path, f"unknown method '{u}'")
        known = [m for m in uses if m]
        if known and g.get("level") in LEVELS:
            floor = min(LEVELS.index(m["level"]) for m in known)
            if LEVELS.index(g["level"]) > floor:
                err(path, f"level '{g['level']}' exceeds its weakest method ('{LEVELS[floor]}')")
        needed = {a for m in known for a in m.get("assumptions", [])}
        for a in sorted(needed - set(g.get("assumptions", []))):
            err(path, f"assumption '{a}' of a used method is not declared")
        if not (ROOT / "specs/claims/README.md").read_text().count(f"`{g.get('claim')}`"):
            err(path, f"claim type '{g.get('claim')}' is not in specs/claims/README.md")
        check_lean(path, g.get("lean", {}).get("instances", []))

    for f in sorted((ROOT / "methods").rglob("*")):
        if f.suffix in {".py", ".lean", ".ts", ".rs"} and f.resolve() not in covered:
            errors.append(f"{f.relative_to(ROOT)}: not covered by any catalog/methods manifest (every method needs a level)")
    return errors, methods, guarantees


def table(methods, guarantees):
    rows = ["| Level | Method | Mode | Kind | Lean correctness |", "| --- | --- | --- | --- | --- |"]
    order = sorted(methods.items(), key=lambda kv: (-LEVELS.index(kv[1]["level"]), kv[1]["id"]))
    for path, m in order:
        thm = ", ".join(f"`{n.rsplit('.', 1)[-1]}`" for n in m.get("lean", {}).get("correctness", [])[:2]) or "none"
        rows.append(f"| **{m['level']}** | [{m['name']}](methods/{path.name}) | {m.get('mode', '-')} | {m['kind']} | {thm} |")
    rows += ["", "| Level | Guarantee | Uses | Assumptions |", "| --- | --- | --- | --- |"]
    for path, g in guarantees.items():
        rows.append(f"| **{g['level']}** | [{g['name']}](guarantees/{path.name}) | {', '.join(g['uses'])} | {', '.join(g['assumptions'])} |")
    return "\n".join(rows)


def main():
    errors, methods, guarantees = check()
    readme = ROOT / "catalog/README.md"
    text = readme.read_text(encoding="utf-8")
    start, end = text.index(TABLE_START) + len(TABLE_START), text.index(TABLE_END)
    fresh = text[:start] + "\n" + table(methods, guarantees) + "\n" + text[end:]
    if "--write" in sys.argv:
        readme.write_text(fresh, encoding="utf-8")
    elif fresh != text:
        errors.append("catalog/README.md table is stale: run tests/regression/check_catalog.py --write")
    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    counts = {lvl: sum(m["level"] == lvl for m in methods.values()) for lvl in reversed(LEVELS)}
    print(f"[OK] {len(methods)} methods ({counts}), {len(guarantees)} guarantees")
    return 0


if __name__ == "__main__":
    sys.exit(main())
