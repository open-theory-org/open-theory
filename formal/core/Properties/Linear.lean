import Models.Linear.Basic
import Properties.Interface

/-!
# Linear models provide a decision and a score

The properties `Decides` and `MonotoneIn` of `Properties/Interface.lean` apply to them as they
are; the cards `robust-decision` and `monotone-feature` each gain a claim type for them.
-/

namespace OpenTheory.Checks.Linear

instance : HasDecision LinearModel (ℕ → ℝ) Bool := ⟨fun m x c => (m.Approves x ↔ c = true)⟩

noncomputable instance : HasScore LinearModel (ℕ → ℝ) := ⟨LinearModel.score⟩

end OpenTheory.Checks.Linear
