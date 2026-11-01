+++
id = "mlp-exact"
observable = "exact-output"
domain = "region"
aggregate = "all"
models = ["relu-mlp"]
lean = ["OpenTheory.Checks.MLP.check"]
sound = []         # open: the theorem that acceptance implies the claim is not proved yet
assumptions = ["A3-model-binding"]
references = [{ key = "harvey2009kronecker", relation = "background" }]
+++
# Claim: exact output (`mlp-exact`)

**Statement.** A ReLU network with integer weights outputs exactly `Y` on the input `x` (a region
with one point).

**Lean.** The packed check `Checks.MLP.check`. Its meaning (acceptance implies the outputs of
`Exact.reluMLP`) is not proved yet, so the method is `experimental`.
