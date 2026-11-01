+++
id = "tree-robust"
observable = "decision"
domain = "region"
aggregate = "all"
models = ["tree-ensemble"]
lean = ["OpenTheory.Checks.Tree.robustCert", "OpenTheory.Checks.Tree.robustCertK", "OpenTheory.Checks.Tree.robustCert_sound"]
sound = ["OpenTheory.treeRobust_sound"]
assumptions = ["A3-model-binding", "A11-tree-translation"]
references = [{ key = "chen2019robustness", relation = "adapts", note = "per-tree reachable-leaf bounds summed over the ensemble: a sound, incomplete check proved in Lean, instead of an exact search" }]
+++
# Claim: robust decision of a tree ensemble on a box (`tree-robust`)

**Statement.** The ensemble's decision is `c` on every real input of the box `B` (for example,
every applicant within ±5% of this one's income and debt, the other features fixed).

**Spec.** Observable: the property "the decision is `c`". Domain: the region `{x | B.Mem x}`.
Aggregate: `all`. `OpenTheory.treeRobust_sound` proves `Sound` with `δ = 0`: an accepted claim
is true.

**Check.** `Checks.Tree.robustCertK` (what `ot_kernel` evaluates; equal to `robustCert` by
`robustCertK_eq`). The certificate gives one bound per tree; the kernel walks each tree, keeping
the branches a point of `B` can reach, checks every reached leaf against its bound, and compares
`base + Σ bounds` with `τ`. Sound (`robustCert_sound`); incomplete, since trees sharing a feature
cannot all reach their extreme leaves at once, so a rejection is not a counterexample. The
producer computes the tightest bounds (`methods/trees/tree_certificate.py`).

**Does not cover.** Inputs outside `B`; preprocessing before the model (scaling, binning, one-hot);
whether the certified model is the deployed one (A3); the translation from the deployed
model (A11): missing values, categorical splits.
