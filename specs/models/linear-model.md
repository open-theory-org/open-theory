+++
id = "linear-model"
family = "Linear and logistic-regression models: approve when τ ≤ bias + Σ w_f x_f (a probability threshold p is the score threshold log(p / (1 − p)))"
type = "OpenTheory.Checks.Linear.LinearModel"     # the Lean type a spec quantifies over (Spec M X: M)
implements = ["OpenTheory.HasDecision", "OpenTheory.HasScore"]   # instances in Properties/ (the properties it can be asked)
lean = ["OpenTheory.Checks.Linear.LinearModel", "OpenTheory.Checks.Linear.LinearModel.score", "OpenTheory.Checks.Linear.LinearModel.Approves"]
references = [{ key = "hosmer2013applied", relation = "background" }]
+++
# Model: linear and logistic-regression model

The score is `bias + Σ_f w_f · x_f` on a real feature vector; the model approves when the score is
at least `τ`. A logistic regression approves when `σ(score) ≥ p`, the same decision with
`τ = log (p / (1 − p))`.

**Exact checks.** The score is linear, so its least and greatest values on a box are at the
corners the weights' signs pick: robustness on a box and monotonicity in a feature are decided
exactly, not only soundly, in one pass over the weights (`Checks/Linear.lean`).

**Translation.** The verifier scales the intercept and the coefficients (doubles, hence dyadic)
exactly, rounds the threshold towards the claim and the box outwards (A11).
