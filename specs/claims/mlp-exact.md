+++
id = "mlp-exact"
observable = "exact-output"
domain = "region"
aggregate = "all"
models = ["relu-mlp"]
lean = ["OpenTheory.Checks.MLP.check", "OpenTheory.Checks.MLP.check_spec", "OpenTheory.Checks.MLP.run_spec", "OpenTheory.Checks.MLP.layerOk_spec", "OpenTheory.Checks.MLP.mlpExact_sound"]
claim_types = ["OpenTheory.ClaimTypes.mlpExact"]
assumptions = ["A3-model-binding"]
references = [{ key = "harvey2009kronecker", relation = "background" }]
+++
# Claim: exact output (`mlp-exact`)

**Statement.** A ReLU network with integer weights, `D → h₁ → … → o`, outputs exactly the scores
`Y` on the input `x` (a region with one point).

**Spec.** Observable: the property `Exact.Net.OutputIs y` (the network's integer forward pass on
`x` is `y`). Domain: the region `{x}`. Aggregate: `all`. `ClaimTypes.mlpExact D hs o` proves `Sound`
with `δ = 0` (`Checks.MLP.mlpExact_sound`).

**Check.** `Checks.MLP.check`, on packed integers: one product per layer for all its dot products
(Kronecker substitution), with the layer's dot products, pre-activations and activations as
intermediate quantities the kernel checks. **Proved sound** (`Specs/MLPExact.lean`):
`layerOk_spec` (an accepted layer computes `W·u + b` on the stored weights), `run_spec` and
`check_spec` (an accepted check computes the stored network's forward pass), `run_toParams` (that
forward pass is `Exact.reluMLP`'s run). 0.4 ms for 1,210 parameters, 2 ms for 101,770
(`docs/benchmarks.md`).

**Does not cover.** Other inputs; whether the stored network is the deployed one (A3);
floating-point deployments, unless the integer network is the deployed one.
