+++
id = "tree-ensemble"
family = "Decision-tree ensembles (gradient boosting, random forests) with a threshold decision: approve when τ ≤ base + Σ trees, integer-scaled thresholds and leaves"
type = "OpenTheory.Checks.Tree.Ensemble"     # the Lean type a spec quantifies over (Spec M X: M)
lean = ["OpenTheory.Checks.Tree.Tree", "OpenTheory.Checks.Tree.Ensemble", "OpenTheory.Checks.Tree.Tree.eval", "OpenTheory.Checks.Tree.Ensemble.score"]
references = [{ key = "devos2021versatile", relation = "background" }, { key = "chen2019robustness", relation = "background" }]
+++
# Model: tree ensemble

A tree sends an input to its low branch when the split feature is at most the threshold
(`x f ≤ t`, the LightGBM and XGBoost convention), and returns a leaf. The ensemble's score is a
base plus the sum of its trees' leaves; it approves when the score is at least `τ`.

**One data structure, two readings.** The tree is the same term in the check (`Checks/Tree.lean`,
core Lean, integers only) and in the proof (`Models/Tree/Basic.lean`, real inputs), so no agreement
theorem is needed. The producer scales each feature by a positive factor so that its thresholds
are integers, and all leaves and `τ` by one positive factor; neither changes a decision.
Floating-point thresholds are dyadic rationals, so the scaling is exact.

**Not yet covered.** Missing-value routing (`default_left`), categorical splits, and the sigmoid
of the score (a threshold on the probability is a threshold on the score).
