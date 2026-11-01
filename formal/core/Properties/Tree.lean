import Models.Tree.Basic
import Properties.Interface

/-!
# Tree ensembles provide a decision and a score

An ensemble decides `true` (approve) when `τ ≤ score`, and its score is `base + Σ trees`; the
properties `Decides` and `MonotoneIn` of `Properties/Interface.lean` apply to it as they are.
-/

namespace OpenTheory.Checks.Tree

instance : HasDecision Ensemble (ℕ → ℝ) Bool := ⟨fun e x c => (e.Approves x ↔ c = true)⟩

noncomputable instance : HasScore Ensemble (ℕ → ℝ) := ⟨Ensemble.score⟩

end OpenTheory.Checks.Tree
