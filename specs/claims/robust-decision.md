+++
id = "robust-decision"
observable = "decision"
domain = "region"
aggregate = "all"
models = ["relu-mlp", "tree-ensemble", "linear-model"]
lean = ["OpenTheory.OnRegion.certify", "OpenTheory.OnRegion.certify_sound", "OpenTheory.Checks.Tree.robustCert", "OpenTheory.Checks.Tree.robustCertK", "OpenTheory.Checks.Tree.robustCert_sound", "OpenTheory.Checks.Linear.robust", "OpenTheory.Checks.Linear.robust_sound", "OpenTheory.Checks.Linear.robustPackedN", "OpenTheory.Checks.Linear.robustPacked_sound"]
claim_types = ["OpenTheory.ClaimTypes.robustRegion", "OpenTheory.ClaimTypes.treeRobust", "OpenTheory.ClaimTypes.linearRobust", "OpenTheory.ClaimTypes.linearRobustPacked"]
assumptions = ["A3-model-binding", "A11-model-translation"]
references = [
  { key = "gowal2018ibp", relation = "adapts", note = "integer interval propagation with a kernel-checked soundness proof for every ReLU MLP" },
  { key = "chen2019robustness", relation = "adapts", note = "per-tree reachable-leaf bounds summed over the ensemble: a sound, incomplete check proved in Lean, instead of an exact search" },
]
+++
# Claim: the decision is robust on a box (`robust-decision`)

**Statement.** The model decides `c` on every real input of the box `B` (for example every
applicant within ±5% of this one's income and debt, the other features fixed). One spec for every
family that provides a decision (`HasDecision`, `Properties/Interface.lean`); one claim type per
family:

| Family | Claim type | Check | δ |
| --- | --- | --- | --- |
| ReLU networks (`relu-mlp`) | `ClaimTypes.robustRegion` | integer interval propagation, `OnRegion.certify` | 0 |
| tree ensembles (`tree-ensemble`) | `ClaimTypes.treeRobust` | per-tree bounds, `Checks.Tree.robustCertK` | 0 |
| linear and logistic-regression models (`linear-model`) | `ClaimTypes.linearRobust` | the corner the weights' signs pick, `Checks.Linear.robust` (exact) | 0 |
| linear models, every feature bounded (`linear-model`) | `ClaimTypes.linearRobustPacked` | the same corner bound by four packed products, `Checks.Linear.robustPackedN` (exact, cost independent of the width) | 0 |

**Spec.** Observable: the property `Decides c`. Domain: the region of the box. Aggregate: `all`.
Each claim type's `sound` proves `Sound` with `δ = 0`: an accepted claim is true.

**Networks.** The check `OnRegion.certify` propagates integer intervals through the network
(`Net.box_sound`, proved once for every network built from exact primitives). No catalog method
yet: the theorem and the kernel check exist, without a producer or a conformance test.

**Trees.** The check `Checks.Tree.robustCertK` (what `ot_kernel` evaluates; equal to `robustCert` by
`robustCertK_eq`). The certificate gives one bound per tree; the kernel walks each tree, keeping
the branches a point of `B` can reach, checks every reached leaf against its bound, and compares
`base + Σ bounds` with `τ`. Sound (`robustCert_sound`); incomplete, since trees sharing a feature
cannot all reach their extreme leaves at once, so a rejection is not a counterexample. The
producer computes the tightest bounds (`methods/trees/tree_certificate.py`).

**Linear models.** The check `Checks.Linear.robust` computes the least (or greatest) score on the
box, at the corner the weights' signs pick, in one pass over the weights; it is exact. Sound
(`Checks.Linear.robust_sound`). When every feature is bounded, the verifier sends the packed check
`Checks.Linear.robustPackedN` instead: the weights split as `w⁺ − w⁻` and the bounds, shifted to be
non-negative, are base-2^B digits, and the same corner bound comes from two big-integer products,
so the kernel's work does not grow with the number of features (0.25 ms at 10, 0.8 ms at 1,000;
[docs/benchmarks.md](../../docs/benchmarks.md)). Sound (`Checks.Linear.robustPacked_sound`), about the
model and box the request stores; the conformance test unpacks them and compares.

**Assumptions.** A3 (the certified model is the deployed one) for all; A11 (the translation from the
model file) for trees and linear models.

**Does not cover.** Inputs outside the box; preprocessing before the model (scaling, binning,
one-hot); missing values and categorical splits (trees, A11); floating-point deployments of a
network.
