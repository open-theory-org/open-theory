+++
id = "robust-region"
property = "predicts"
scope = "region"
models = ["relu-mlp"]
lean = ["OpenTheory.OnRegion.certify", "OpenTheory.OnRegion.certify_sound", "OpenTheory.OnRegion.robust_of_certify"]
sound = ["OpenTheory.onRegion_sound"]
checks = []
methods = []
assumptions = ["A3-model-binding"]
references = [{ key = "gowal2018ibp", relation = "adapts", note = "integer interval propagation with a kernel-checked soundness proof for every ReLU MLP" }]
+++
# Claim: robust on a region (`robust-region`)

**Statement.** The TorchLean model predicts class `c` on every real input of an integer box (for
example the ℓ∞ ball of radius `ε` around an input), and the box is not empty.

**Lean.** The check `OnRegion.certify`; its meaning `OnRegion.certify_sound` (and the ℓ∞ form
`robust_of_certify`), and as an instance of the generic guarantee, `onRegion_sound` (`δ = 0`).

**Level.** None yet: the theorem and the kernel check exist, but no method, catalog entry or
conformance test.

**Does not cover.** Inputs outside the box, floating-point deployments (A3).
