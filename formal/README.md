# formal/: the mathematics (Lean 4 + Mathlib)

Library `OpenTheory`, root module [`OpenTheory.lean`](OpenTheory.lean). Modules live in `formal/core/<Layer>/` and are named by layer (`Foundations.…`, `Models.…`, `Theory.…`, `Specs.…`). Declarations keep the `OpenTheory.` namespace.

`formal/core/` is built bottom-up. Each layer imports only its own layer and the ones above it in this table. Tensors, layers and their composition come from [TorchLean](https://github.com/lean-dojo/TorchLean).

| Layer | Contents |
| --- | --- |
| [Foundations](core/Foundations/) | Maths not specific to ML: data and samples, probability (including the binomial tail), linear algebra, ridge and first-order optimization, exact arithmetic (Kronecker substitution), Hironaka |
| [Models](core/Models/) | Model semantics: MLP, attention, transformer, residual, quantized MLP and its packed kernel runner |
| [Properties](core/Properties/) | Yes/no tests on one input (empty, planned) |
| [Theory](core/Theory/) | Theorems, grouped by what they are about (see below) |
| [Specs](core/Specs/) | Claim templates and their instances: held-out error, Occam and PAC-Bayes certificates for quantized MLPs |
| [vendors](vendors/) | Narrow, provenance-recorded ports (FoML, StatLean, SLT) |

`Theory/` is grouped by the object a theorem studies:

| Folder | Studies | Contents |
| --- | --- | --- |
| [Function](core/Theory/Function/) | one fixed model | expressivity, attention head-ablation fidelity, logit stability |
| [Learning](core/Theory/Learning/) | data → chosen model | generalization: finite classes, covering, Rademacher, PAC-Bayes, MLP, attention and transformer risk |
| [Training](core/Theory/Training/) | the training run | gradient flow, dynamics, parameterization (NTK, μP), singular learning theory and the plateau |
| [Representation](core/Theory/Representation/) | internal features | features, Gram matrices, alignment, feature-learning advantage |
| [Agents](core/Theory/Agents/) | a policy in an environment | empty: agent systems, decision theory, causal inference |

Rules: no `sorry` outside declared open targets, and only `propext`, `Classical.choice` and `Quot.sound`. See [docs/contributing](../docs/contributing/).
