# formal/: the mathematics (Lean 4 + Mathlib)

Library `OpenTheory`, root module [`OpenTheory.lean`](OpenTheory.lean). Modules live in `formal/core/<Area>/` and are named by area (`Foundations.…`, `Verification.…`). Declarations keep the `OpenTheory.` namespace.

| Area | Contents |
| --- | --- |
| [Foundations](core/Foundations/) | Data, model semantics (MLP, attention, transformer, quantized MLP), optimization, probability, linear algebra, Hironaka |
| [LearningTheory](core/LearningTheory/) | Generalization, training dynamics, parameterization, singular learning theory and the gradient-descent plateau |
| [Representations](core/Representations/) | Features, Gram matrices, alignment, expressivity |
| [Interpretability](core/Interpretability/) | Attention head-ablation fidelity, logit stability |
| [CausalInference](core/CausalInference/) | empty |
| [DecisionTheory](core/DecisionTheory/) | empty |
| [Alignment](core/Alignment/) | empty |
| [AgentSystems](core/AgentSystems/) | empty |
| [Verification](core/Verification/) | Soundness of checks: the binomial test-set bound, Occam and PAC-Bayes certificates, verified packed inference |
| [vendors](vendors/) | Narrow, provenance-recorded ports (FoML, StatLean, SLT) |

Rules: no `sorry` outside declared open targets, and only `propext`, `Classical.choice` and `Quot.sound`. See [docs/contributing](../docs/contributing/).
