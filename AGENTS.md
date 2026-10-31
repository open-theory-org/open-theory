# OpenTheory

A **Lean 4 + Mathlib** repository with a Patrick Massot `leanblueprint`. It is not a Next.js app.
Layout: [docs/architecture/repository.md](docs/architecture/repository.md).

## Source of truth

- Mathematics: `formal/core/**/*.lean` (layers `Checks.…` → `Foundations.…` → `Models.…` → `Properties.…` → `Theory.…` → `Scopes.…` → `Specs.…`, each importing only earlier layers, `Checks` only Lean's core; declarations in `OpenTheory.`) and `blueprint/src/content.tex`
- Assurance levels: `specs/protocols/assurance-levels.md`, with one manifest per method in `catalog/methods/`
- Platform feed: `blueprint/blueprint.json` (regenerate with `python3 blueprint/export_blueprint.py`)
- Local agents: `interfaces/mcp/` (stdio). Do not add an HTTP API on this repo.

## Honesty rules

- Every `\lean{Name}` in `content.tex` must be a real declaration (`python3 tests/regression/check_lean_decls.py`).
- `\leanok` on a lemma/conjecture **proof** means no `sorry`. Statement-only `\leanok` means the claim is in Lean and may still be `sorry`.
- Do not mark stubs, `True` fillers, or trivial `use` proofs as verified.
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` on open targets.
- A method is `verified` only with a Lean specification, a kernel-checked correctness theorem and a conformance test. Floating-point implementations are at most `specified`. `research/` is experimental (`python3 tests/regression/check_catalog.py`).

## Commands

```bash
lake build
lake env lean --run verifier/backends/formal/audit_axioms.lean
python3 tests/regression/check_lean_decls.py
python3 tests/regression/check_catalog.py
python3 blueprint/export_blueprint.py blueprint/blueprint.json
python3 tests/conformance/heldout_verify.py   # ot verify conformance
```
