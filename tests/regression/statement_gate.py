#!/usr/bin/env python3
"""Flag theorem statements that compile but say little (see tests/regression/audit/notes.md).

Lean checks proofs, not meaning. This gate looks at *statements* and flags the
patterns the 2026-10 audit found in the C/D files:

  toy-formula     every variable is a scalar and the statement uses a repo `def`
                  whose arguments are all scalars (an invented formula)
  flag-compiler   the statement is about a Bool/enum "prescribe/classify/compile"
                  function, or the proof is a single rfl/decide
  trivial-exists  the conclusion is an existential closed in a few lines
  bundle          a "grand/master/unification" conjunction of other results
  unused-hyp      a hypothesis named `_h...`: stated but never used
  constant-def    a `def` whose body is a literal or one of its arguments

Usage:
  python3 tests/regression/statement_gate.py                      # report over formal/core/
  python3 tests/regression/statement_gate.py --check tests/regression/audit/grades.csv
  python3 tests/regression/statement_gate.py --fail formal/core/Foo.lean  # CI: exit 1 on flags
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "formal" / "core"

THM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma)\s+(\S+)")
DEF = re.compile(r"^\s*(?:noncomputable |private |protected )*(?:def|abbrev)\s+(\S+)")
BOUNDARY = re.compile(
    r"^\s*(?:@\[|/--|/-!|theorem |lemma |def |noncomputable |private |protected |structure |"
    r"inductive |instance |abbrev |class |namespace |end |section |open |variable |omit |#)"
)
SCALAR = re.compile(r"^(?:ℝ|ℕ|ℚ|ℤ|Bool|NNReal|ℝ≥0)$")
RELATION = re.compile(r"[<>≤≥=≠↔→∀∃¬∧∨]|Lipschitz|Integrable|Measurable|Is[A-Z]")
FLAG_FN = re.compile(r"^(?:prescribe|classify|compile|dispatch|select|synthesize|verify)[A-Z]")
BUNDLE_NAME = re.compile(r"grand|master|unification|synthesis|atlas|ultimate|closure|universal_")
SHORT_PROOF = re.compile(r"^\s*(?:by\s+)?(?:rfl|decide|native_decide|norm_num|simp|trivial)\s*$")
# Scalar defs whose meaning is a proved theorem, not an invented formula: `binomCdf` is the law of
# the error count (`BinomialTail.sampleLaw_count_le`), `tailNumerator` its integer numerator
# (`BinomialTail.tailNumerator_eq`). The `Checks` decision-procedure parts are pinned to their
# Mathlib meaning: `popWord`/`popTree` (`PoolRate.popWord_eq`, `popTree_eq`), `hornerState`,
# `tailFast` (`PoolRate.hornerState_eq`, `tailFast_eq`). Statements about them are not toy formulas.
VETTED_DEFS = {"binomCdf", "tailNumerator", "popWord", "popTree", "hornerState", "tailFast"}


def blocks(lines: list[str], start: int) -> tuple[str, int]:
    end = start + 1
    while end < len(lines) and not BOUNDARY.match(lines[end]):
        end += 1
    return "\n".join(lines[start:end]), end


def split_top(text: str, sep: str) -> int:
    """Index of the first `sep` at bracket depth 0, or -1."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(sep, i):
            return i
    return -1


def binders(header: str) -> tuple[list[tuple[str, str]], str]:
    """Parse `(a b : T) {h : P}` groups after the name; return binders and conclusion."""
    out: list[tuple[str, str]] = []
    i = 0
    while i < len(header) and header[i] in " \n\t([{⦃":
        if header[i] in " \n\t":
            i += 1
            continue
        close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}[header[i]]
        depth, j = 0, i
        while j < len(header):
            if header[j] in "([{⦃":
                depth += 1
            elif header[j] in ")]}⦄":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        group = header[i + 1:j]
        if close != "]" and ":" in group:
            names, typ = group.split(":", 1)
            for n in names.split():
                out.append((n, " ".join(typ.split())))
        i = j + 1
    rest = header[i:].strip()
    return out, rest[1:].strip() if rest.startswith(":") else rest


def scan(paths: list[Path]):
    scalar_defs: set[str] = set()
    flag_defs: set[str] = set()
    const_defs: list[tuple[Path, int, str]] = []
    theorems = []
    for path in paths:
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if m := DEF.match(line):
                body, _ = blocks(lines, i)
                name = m.group(1).split(".")[-1]
                k = split_top(body, ":=")
                head, value = (body[:k], body[k + 2:]) if k >= 0 else (body, "")
                params, ret = binders(head[m.end():])
                types = [t for _, t in params]
                if types and all(SCALAR.match(t) for t in types) and SCALAR.match(ret.strip() or "x"):
                    scalar_defs.add(name)
                if FLAG_FN.match(name):
                    flag_defs.add(name)
                v = value.split("/--")[0].strip()
                if re.fullmatch(r"-?\d+(?:\.\d+)?|true|false", v) or (v and v in {n for n, _ in params}):
                    const_defs.append((path, i + 1, name))
            elif m := THM.match(line):
                body, _ = blocks(lines, i)
                k = split_top(body, ":=")
                stmt, proof = (body[:k], body[k + 2:]) if k >= 0 else (body, "")
                theorems.append((path, i + 1, m.group(1), stmt[m.end():], proof))
    return scalar_defs, flag_defs, const_defs, theorems


def flags_for(name, header, proof, scalar_defs, flag_defs):
    params, concl = binders(header)
    variables = [(n, t) for n, t in params if not RELATION.search(t)]
    used = set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", header))
    out = []
    if variables and all(SCALAR.match(t) for _, t in variables) and used & (scalar_defs - VETTED_DEFS):
        out.append("toy-formula")
    if used & flag_defs or SHORT_PROOF.match(proof.strip().split("\n")[0]) and "Bool" in header:
        out.append("flag-compiler")
    proof_lines = len([l for l in proof.splitlines() if l.strip()])
    if concl.startswith("∃") and proof_lines <= 4:
        out.append("trivial-exists")
    if BUNDLE_NAME.search(name) or concl.count("∧") >= 8:
        out.append("bundle")
    if any(n.startswith("_h") for n, _ in params):
        out.append("unused-hyp")
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", type=Path, help="limit to these .lean files")
    ap.add_argument("--check", type=Path, help="compare file flag rates with an audit grades.csv")
    ap.add_argument("--fail", action="store_true", help="exit 1 if any theorem is flagged")
    args = ap.parse_args()

    all_paths = sorted(LEAN_ROOT.rglob("*.lean"))
    scalar_defs, flag_defs, const_defs, theorems = scan(all_paths)
    targets = {p.resolve() for p in args.files} or {p.resolve() for p in all_paths}

    per_file: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    kinds: Counter[str] = Counter()
    flagged = []
    for path, line, name, header, proof in theorems:
        if path.resolve() not in targets:
            continue
        rel = str(path.relative_to(LEAN_ROOT)).removesuffix(".lean")
        f = flags_for(name, header, proof, scalar_defs, flag_defs)
        per_file[rel][1] += 1
        if f:
            per_file[rel][0] += 1
            kinds.update(f)
            flagged.append((path, line, name, f))
    for path, line, name in const_defs:
        if path.resolve() in targets:
            flagged.append((path, line, name, ["constant-def"]))
            kinds["constant-def"] += 1

    total = sum(n for _, n in per_file.values())
    hit = sum(h for h, _ in per_file.values())
    print(f"{hit}/{total} theorems flagged ({100 * hit / max(total, 1):.0f}%); by kind: {dict(kinds)}")

    if args.check:
        grades = {r["file"]: r["grade"] for r in csv.DictReader(args.check.open()) if r["repo"] == "OpenTheory"}
        rate = {f: h / n for f, (h, n) in per_file.items() if n}
        bad = {f for f, g in grades.items() if g in "CD" and f in rate}
        good = {f for f, g in grades.items() if g in "AB" and f in rate}
        for cut in (0.25, 0.5):
            caught = sum(rate[f] >= cut for f in bad)
            false_pos = sum(rate[f] >= cut for f in good)
            print(f"files with >= {cut:.0%} flagged: C/D caught {caught}/{len(bad)}, A/B wrongly flagged {false_pos}/{len(good)}")
        for f in sorted(good, key=lambda f: -rate[f])[:5]:
            print(f"  A/B file with most flags: {f} ({rate[f]:.0%})")
        for f in sorted(bad, key=lambda f: rate[f])[:5]:
            print(f"  C/D file with fewest flags: {f} ({rate[f]:.0%})")
    elif args.files or args.fail:
        for path, line, name, f in flagged:
            print(f"{path.relative_to(ROOT)}:{line}: {name}: {', '.join(f)}")
    return 1 if args.fail and flagged else 0


if __name__ == "__main__":
    sys.exit(main())
