import Checks.Linear
import Models.Tree.Basic

/-!
# Linear and logistic-regression models: exact semantics

The proof form of the models of `Checks/Linear.lean`: integer weights, real inputs indexed by
feature (`ℕ → ℝ`, as for trees). A logistic regression approves when its probability is at least
`p`, that is when its score is at least `log (p / (1 − p))`; the producer gives that score
threshold as `τ`, rounded in the direction that keeps the claim sound.
-/

namespace OpenTheory.Checks.Linear

/-- A linear model that approves when `τ ≤ bias + Σ_f w_f · x_f`. -/
structure LinearModel where
  bias : Int
  τ : Int
  weights : List Int

/-- `Σ_i w_i · x_{f+i}`. -/
noncomputable def scoreFrom : List Int → ℕ → (ℕ → ℝ) → ℝ
  | [], _, _ => 0
  | w :: ws, f, x => (w : ℝ) * x f + scoreFrom ws (f + 1) x

/-- The model's score on an input. -/
noncomputable def LinearModel.score (m : LinearModel) (x : ℕ → ℝ) : ℝ := m.bias + scoreFrom m.weights 0 x

/-- The model approves the input. -/
def LinearModel.Approves (m : LinearModel) (x : ℕ → ℝ) : Prop := (m.τ : ℝ) ≤ m.score x

end OpenTheory.Checks.Linear
