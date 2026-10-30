# Contributing

## The gold standard

OpenTheory distinguishes **verified** methods (a wrong result cannot be accepted) from
**specified** and **experimental** ones. Definitions are in
[specs/protocols/assurance-levels.md](../../specs/protocols/assurance-levels.md). In short:

- A new method goes in `methods/<kind>/` **with** a manifest in `catalog/methods/`. CI fails otherwise.
- To claim `verified`, give the Lean specification, the correctness theorem, the mode (`verified-implementation` or `verified-checker`) and a conformance test that rejects a forgery.
- A floating-point implementation of a theorem about `ℝ` is `specified`, not `verified`.
- Research code goes in `research/` and is experimental by definition.

## Honesty rules (Lean)

- Every `\lean{Name}` in `blueprint/src/content.tex` must be a real declaration.
- `\leanok` on a proof means no `sorry`. Do not mark stubs, `True` fillers or trivial `use` proofs as verified.
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` on declared open targets only. No `native_decide`.

## Before a PR

```bash
lake build
lake env lean --run verifier/backends/formal/audit_axioms.lean
python3 tests/regression/check_lean_decls.py
python3 tests/regression/check_catalog.py
python3 blueprint/export_blueprint.py --check
python3 -m unittest discover -s tests/regression && python3 -m unittest discover -s tests/integration
```
