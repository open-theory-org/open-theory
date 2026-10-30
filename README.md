# OpenTheory

Open foundations for **verifiable claims about AI systems**: the mathematics in Lean 4, the
claim and certificate specifications, a verifier anyone can run, and conformance tests.

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.34.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib 4](https://img.shields.io/badge/Mathlib_4-pinned-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-yellow.svg)](LICENCE)

## The gold standard: formally verified methods

Every method carries one of three [assurance levels](specs/protocols/assurance-levels.md),
and CI enforces them:

| Level | Meaning |
| --- | --- |
| **verified** | A Lean specification plus a kernel-checked correctness theorem. Either the kernel runs the algorithm, or it checks the output of untrusted code. **A wrong result cannot be accepted.** |
| **specified** | The intended result is defined in Lean, but the code that runs (for example in floating point) is not proved to compute it. |
| **experimental** | Evidence, not a guarantee. Everything in `research/`. |

The current methods and their levels are listed in [catalog/](catalog/README.md).

**Flagship:** [examples/certified_accuracy](examples/certified_accuracy/README.md). It is a
population-error certificate for a trained network, and the Lean kernel accepts it only if it is true.
It accepts the honest claim and rejects four forgeries (`tests/conformance/certified_accuracy.sh`).

## Layout

```text
specs/       DEFINE      claim types, assumptions, evidence, certificate formats, assurance levels, protocols
formal/      PROVE       Lean (`formal/core/<Area>/`): Foundations, LearningTheory, Representations,
                         Interpretability, CausalInference, DecisionTheory, Alignment, AgentSystems, Verification
methods/     PRODUCE     untrusted evidence producers (statistical, neural, whitebox, evaluations, causal, runtime, zk_proving)
verifier/    CHECK       verify engine (`ot verify`), axiom audit; attestations planned
interfaces/  ACCESS      `ot` CLI, Python SDK, MCP (local stdio)
catalog/     DISCOVER    method and guarantee manifests with levels
research/    ADVANCE     experiments, literature, hypotheses (experimental by definition)
examples/    DEMONSTRATE certified_accuracy; interpretability, agent safety, causal, private (planned)
tests/       QUALITY     conformance, integration, adversarial, regression
docs/        EXPLAIN     concepts, tutorials, architecture, contributing, PLAN
blueprint/   leanblueprint source (content.tex) and blueprint.json
```

Details: [docs/architecture/repository.md](docs/architecture/repository.md). Roadmap: [docs/PLAN.md](docs/PLAN.md).

## Build and check

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake exe cache get
lake build
lake env lean --run verifier/backends/formal/audit_axioms.lean   # no sorry, standard axioms only
python3 tests/regression/check_lean_decls.py                     # blueprint names are real
python3 tests/regression/check_catalog.py                        # assurance levels hold
tests/conformance/certified_accuracy.sh                          # 1 accept, 4 rejects (~2 min)
python3 tests/conformance/heldout_verify.py                      # ot verify: 1 accept, 14 rejects (~3 min)
```

## Check a certificate

```bash
interfaces/cli/ot certify heldout examples/certified_accuracy/model/pacbayes_digits64.json --out /tmp/cert
interfaces/cli/ot verify /tmp/cert      # ACCEPTED, the claim, its level, assumptions, trusted base, scope
```

A certificate is a folder of data (`certificate.json`, `model.json`, `heldout.json`) with no Lean code in it.
`ot verify` writes the Lean statement from the claim template, re-runs the network in the Lean kernel
and checks the binomial bound. See [specs/certificates](specs/certificates/README.md).

Codespaces: `.devcontainer/` (Lean + `leanblueprint`).

## Blueprint

`\leanok` on a statement means the statement is in Lean (it may still contain `sorry`). `\leanok` inside
`\begin{proof}` means the proof has no `sorry`.

```bash
pip install leanblueprint
leanblueprint web && leanblueprint serve
python3 blueprint/export_blueprint.py blueprint/blueprint.json
```

GitHub Pages: <https://matthieu-perso.github.io/open-theory/blueprint/>. See [blueprint/README.md](blueprint/README.md).
The web dashboard is a separate repo and only **reads** `blueprint/blueprint.json`. This repo has no HTTP API.

## MCP (local agents only)

```bash
uv run interfaces/mcp/server.py   # stdio; tools and client setup in interfaces/mcp/README.md
```

## Contribute

See [docs/contributing](docs/contributing/README.md). Do not add axioms. A method without a catalog
manifest fails CI. Results proved so far: [docs/concepts/learning-theory-results.md](docs/concepts/learning-theory-results.md).
