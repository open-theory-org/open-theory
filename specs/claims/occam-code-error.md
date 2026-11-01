+++
id = "occam-code-error"
observable = "wrong"
domain = "distribution"
aggregate = "meanLe"
models = ["quantized-mlp"]
lean = ["OpenTheory.QuantizedMLP.selected_code_certificate"]
claim_types = ["OpenTheory.ClaimTypes.occam"]
assumptions = ["A1-iid", "A3-model-binding", "A4-labels"]
references = [{ key = "blumer1987occam", relation = "implements" }]
+++
# Claim: Occam error bound (`occam-code-error`)

**Statement.** For a model selected from a finite code family using the training data, the
population error is at most the training error plus `ε`, with probability at least `1 − δ`.

**Spec.** Observable: the property "the code errs on `z`" (`classificationLoss a c z = 1`).
Domain: the data distribution. Aggregate: `meanLe p`. `OpenTheory.occam_sound` proves `Sound` for
this `Spec.Target` with `δ = 2·4ᵈ·exp(−2nε²)` over the IID training sample, uniformly over the code
`c` and the bound `p`: the code may be the one training selected. The certificate's acceptance is
"empirical error `+ ε ≤ p`"; the empirical error is the kernel's error count
(`quantized-mlp-kernel-inference`, `empiricalRisk_eq_errorCount`).

**Does not cover.** Data outside the distribution the training sample came from (A1); a code space
other than `4^d` codes; mislabelled data (A4).
