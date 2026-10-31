+++
id = "occam-code-error"
property = "zero-loss"
scope = "population-iid"
models = ["quantized-mlp"]
lean = ["OpenTheory.QuantizedMLP.selected_code_certificate"]
sound = []         # bridge to `Sound` planned: the bound is uniform over every code the learner may select
methods = ["occam-code-certificate"]
checks = []
assumptions = ["A1-iid", "A4-labels"]
references = [{ key = "blumer1987occam", relation = "implements" }]
+++
# Claim: Occam error bound (`occam-code-error`)

**Statement.** For a model selected from a finite code family using the training data, the
population error is at most the training error plus `ε`, with probability at least `1 − δ`.
