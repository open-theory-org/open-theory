# formal/: the mathematics (Lean 4 + Mathlib)

Library `OpenTheory`, root module [`OpenTheory.lean`](OpenTheory.lean). Modules live in `formal/core/<Layer>/` and are named by layer (`Foundations.…`, `Models.…`, `Properties.…`, `Theory.…`, `Scopes.…`, `Specs.…`). Declarations keep the `OpenTheory.` namespace.

`formal/core/` is built bottom-up. Each layer imports only its own layer and the ones above it in this table (`tests/regression/check_layers.py`). Tensors, layers and their composition come from [TorchLean](https://github.com/lean-dojo/TorchLean).

| Layer | Contents |
| --- | --- |
| [Foundations](core/Foundations/) | Maths not specific to ML: data and samples, probability (including the binomial tail), linear algebra, ridge and first-order optimization, exact arithmetic (Kronecker substitution), Hironaka |
| [Models](core/Models/) | Model semantics: MLP, attention, transformer, residual, quantized MLP and its packed kernel runner, and [exact integer networks](core/Models/Exact/) (below) |
| [Properties](core/Properties/) | Yes/no tests on one model output: `Predicts` (strict-margin classification) |
| [Theory](core/Theory/) | Theorems, grouped by what they are about (see below) |
| [Scopes](core/Scopes/) | Which inputs a property covers, as a kernel check with a soundness theorem: `OnRegion` (every real input in an integer box or ℓ∞ ball) |
| [Specs](core/Specs/) | Claim templates and their instances: held-out error, Occam and PAC-Bayes certificates for quantized MLPs |

**Exact integer networks** (`Models/Exact/`). Each model has a proof form (a TorchLean chain over `ℝ`) and a check form (an integer runner the kernel evaluates in milliseconds). A `Prim` pairs one TorchLean primitive with its integer runner and an agreement proof; a `Net` is any composition of `Prim`s. Class theorems are proved once by induction on the composition: `Net.agrees` (the runner equals the TorchLean model) and, for every network whose primitives carry an `IntervalRule`, `Net.box_sound` (interval bounds are sound for every real input). A new architecture from existing primitives needs no proof; a new primitive needs one lemma per contract. Primitives today: `linear` and `relu` on vectors; family: `reluMLP` (all depths and widths).
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
