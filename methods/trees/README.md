# methods/trees/: tree ensembles

[`tree_certificate.py`](tree_certificate.py) (untrusted) reads a LightGBM model dump, scales it
exactly to integers and writes `tree-robust` and `tree-monotone` requests (the trees' checks) for `ot_kernel`, with the
witnesses the kernel checks. Level and sources: [`catalog/methods/tree-ensemble-check.toml`](../../catalog/methods/tree-ensemble-check.toml);
claims: [`specs/claims/robust-decision.md`](../../specs/claims/robust-decision.md),
[`specs/claims/monotone-feature.md`](../../specs/claims/monotone-feature.md). Example:
[`examples/tree_ensemble/`](../../examples/tree_ensemble/).
