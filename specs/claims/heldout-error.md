+++
id = "heldout-error"
observable = "wrong"
domain = "distribution"
aggregate = "meanLe"
models = ["quantized-mlp"]
lean = ["OpenTheory.HeldOut.Claim", "OpenTheory.HeldOut.Claim.of_tail"]
sound = ["OpenTheory.heldOut_sound"]
checks = []        # `ot verify` writes the kernel statement from the template itself
methods = ["heldout-binomial-bound", "quantized-mlp-kernel-inference"]
assumptions = ["A1-iid", "A2-heldout-independent", "A3-model-binding", "A4-labels"]
references = [{ key = "clopper1934use", relation = "implements" }]
+++
# Claim: held-out error (`heldout-error`, v0.1)

**Statement.** For a model `h` fixed before the held-out set is drawn, and `n` IID examples with
`k` errors, if `binomCdf n k p ≤ δ` then `P[ empRisk ≤ k/n ∧ p < risk(h) ] ≤ δ`.

**Lean template.** `OpenTheory.HeldOut.Claim ℓ h s₀ k p δ` in `formal/core/Specs/HeldOut.lean`. It has three parts:

- the loss is `{0,1}`;
- `numErrors ℓ s₀ h ≤ k`;
- `∀ D, P_D^n(numErrors ≤ k ∧ p < risk) ≤ δ`.

It is built only through `Claim.of_tail`, which uses `testSet_bound` and the integer check `d · tailNumerator n k a b ≤ bⁿ`.

**Assumptions.** A1-iid, A2-heldout-independent, A3-model-binding, A4-labels.

**Evidence.** A v0.1 bundle ([certificate format](../certificates/README.md)) holds:

- `model.json`;
- `heldout.json`;
- the claimed `k`, `a / b` and `δ = 1/d`.

**Level.** verified. The kernel recomputes `k` and checks the inequality.

**Reference instance.** [`examples/certified_accuracy/`](../../examples/certified_accuracy/).

**Does not cover.** Distribution shift, other models, or the binding of the Lean function to a deployed system (A3).
