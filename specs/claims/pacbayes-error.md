+++
id = "pacbayes-error"
property = "zero-loss"
scope = "population-iid"
models = ["quantized-mlp"]
lean = ["OpenTheory.PACBayes.catoni_pacBayes"]
sound = []         # bridge to `Sound` planned
methods = ["pacbayes-catoni-certificate"]
checks = []
assumptions = ["A1-iid", "A2-heldout-independent", "A4-labels"]
references = [{ key = "catoni2007pac", relation = "implements" }]
+++
# Claim: PAC-Bayes error bound (`pacbayes-error`)

**Statement.** Catoni's bound for a posterior over a finite code space, with a prior learned on
separate data.
