# methods/trees/: tree ensembles

[`tree_certificate.py`](tree_certificate.py) (untrusted) reads a LightGBM model dump, scales it
exactly to integers and writes `tree-robust` and `tree-monotone` requests for `ot_kernel`, with the
witnesses the kernel checks. Level and sources: [`catalog/methods/tree-ensemble-check.toml`](../../catalog/methods/tree-ensemble-check.toml);
claims: [`specs/claims/tree-robust.md`](../../specs/claims/tree-robust.md),
[`specs/claims/tree-monotone.md`](../../specs/claims/tree-monotone.md). Example:
[`examples/tree_ensemble/`](../../examples/tree_ensemble/).
