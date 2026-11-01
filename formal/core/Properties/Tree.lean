import Models.Tree.Basic
import Properties.Basic

/-!
# Properties of tree ensembles

The two properties the tree claim types use, named so that their cards (`decision`, `monotone`)
bind to them: the decision on one input, and monotonicity on a pair of inputs.
-/

namespace OpenTheory.Checks.Tree

/-- The order a monotonicity claim asks for: `a ≤ b` if increasing, `b ≤ a` if decreasing. -/
def Ordered (up : Bool) (a b : ℝ) : Prop := if up then a ≤ b else b ≤ a

/-- Two inputs that differ only in feature `j`, the second at least the first there. -/
def Raised (j : ℕ) (x x' : ℕ → ℝ) : Prop := (∀ i, i ≠ j → x i = x' i) ∧ x j ≤ x' j

/-- **`decision`.** The ensemble's decision on `x` is `c` (approve when `c`). -/
def Ensemble.Decides (c : Bool) : Property Ensemble (ℕ → ℝ) := fun e x => (e.Approves x ↔ c = true)

/-- **`monotone`.** On a pair `(x, x')` where `x'` raises feature `j` of `x`, the score moves in
the stated direction (up if `up`). -/
def MonotoneIn (j : ℕ) (up : Bool) : Property Ensemble ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun e xx => Raised j xx.1 xx.2 → Ordered up (e.score xx.1) (e.score xx.2)

end OpenTheory.Checks.Tree
