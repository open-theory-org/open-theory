# Repository layout

```text
specs/       DEFINE      claim types, assumptions, evidence, certificate formats, protocols (assurance levels)
formal/      PROVE       Lean library OpenTheory: math and the soundness of every check
methods/     PRODUCE     untrusted evidence producers, one catalog manifest each
verifier/    CHECK       thin layer over the Lean kernel: verify engine (ot verify), axiom audit; attestations planned
interfaces/  ACCESS      ot CLI, Python SDK, MCP (stdio)
catalog/     DISCOVER    method and guarantee manifests with levels (CI-enforced)
research/    ADVANCE     experiments, literature, open hypotheses: experimental by definition
examples/    DEMONSTRATE certified_accuracy (verified) and other examples (planned)
tests/       QUALITY     conformance, integration, adversarial, regression
docs/        EXPLAIN     concepts, tutorials, architecture, contributing, PLAN
blueprint/   leanblueprint source and export (kept at the root, where leanblueprint expects it)
```

**Trust flow.**

1. A `methods/` producer writes a certificate (today, a Lean file).
2. The Lean kernel checks it against a statement in `formal/`.
3. `verifier/` audits the axioms and reports the level from `catalog/` and the assumptions from `specs/`.

Only the kernel and the Lean statements are trusted. Producers are not.

**Lean layout.**

- `lakefile.lean` builds the root module `OpenTheory` (`formal/OpenTheory.lean`), the layer modules (`Checks.…`, `Foundations.…`, `Models.…`, `Properties.…`, `Theory.…`, `Scopes.…`, `Specs.…`) from `formal/core/`, the executables `audit_axioms` and `ot_kernel`, and `CertifiedDigits` from `examples/certified_accuracy/lean/`.
- `formal/core/` is layered bottom-up: Checks → Foundations → Models → Properties → Theory → Scopes → Specs. `Checks` imports only Lean's core, so certificate checks run in a tiny kernel environment. A module imports only its own layer and earlier ones. See [formal/README.md](../../formal/README.md).
- The vendored ports are in `formal/vendors/`.
- The axiom-audit executable is `verifier/backends/formal/audit_axioms.lean`.
