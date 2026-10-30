# OpenTheory overview

OpenTheory formalizes the mathematics behind verifiable claims about AI systems in **Lean 4**,
and labels every method that produces evidence as **verified**, **specified** or **experimental**
([assurance levels](../../specs/protocols/assurance-levels.md)).

The web dashboard is a **different** GitHub repo. It fetches `blueprint/blueprint.json` from this repository. This repository has no HTTP API.

Layout: [../architecture/repository.md](../architecture/repository.md). Lean library areas: [formal/README.md](../../formal/README.md).
Reusable Mathlib and external libraries: [lean-libraries.md](../../research/literature/lean-libraries.md).

## Blueprint convention

Patrick Massot / `leanblueprint`:

- `\lean{Name}`: a declaration in this library or in Mathlib
- `\leanok` on a definition or statement: the statement is formalized
- `\leanok` inside `proof`: the proof is formalized (no `sorry`)
- `\uses{labels}`: the dependency graph

CI refuses `\lean` names that are not declarations.

## Local commands

```bash
lake exe cache get
lake build
lake env lean --run verifier/backends/formal/audit_axioms.lean
python3 tests/regression/check_lean_decls.py
python3 tests/regression/check_catalog.py
python3 blueprint/export_blueprint.py
```
