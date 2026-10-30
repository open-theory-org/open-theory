import Models.Exact.Linear
import Models.Exact.ReLU

/-!
# ReLU multilayer perceptrons

The family of all ReLU MLPs with integer weights, `d → h₁ → … → hₖ → o`, as `Net`s. Members
need no proof of their own: agreement is `Net.agrees`, and the interval rules come from
`reluMLP.intervalRules`, so `Net.box_sound` covers the whole family.
-/

open TorchLean

namespace OpenTheory.Exact

/-- A linear layer followed by ReLU, `[m] → [n]`. -/
def linearReLU (m n : ℕ) : Net m n := .seq (.prim (linear m n)) (.prim (relu n))

/-- The ReLU MLP `d → h₁ → … → hₖ → o`: one `linearReLU` block per hidden width, then a linear
output layer. -/
def reluMLP : (d : ℕ) → List ℕ → (o : ℕ) → Net d o
  | d, [], o => .prim (linear d o)
  | d, h :: hs, o => .seq (linearReLU d h) (reluMLP h hs o)

/-- Interval rules for every member of the family. -/
def reluMLP.intervalRules : (d : ℕ) → (hs : List ℕ) → (o : ℕ) →
    (reluMLP d hs o).Rules IntervalRule
  | d, [], o => linearInterval d o
  | d, h :: hs, o => ((linearInterval d h, reluInterval h), reluMLP.intervalRules h hs o)

/-- **Interval soundness for every ReLU MLP**: every real input in `b` is sent by the TorchLean
model into the integer box computed by interval propagation. -/
theorem reluMLP_box_sound (d : ℕ) (hs : List ℕ) (o : ℕ) (θ : (reluMLP d hs o).Params)
    (b : Box) (x : Tensor ℝ [d]) (hθ : (reluMLP d hs o).valid θ = true) (hx : InBox b x) :
    InBox ((reluMLP d hs o).box (reluMLP.intervalRules d hs o) θ b) ((reluMLP d hs o).eval θ x) :=
  Net.box_sound _ _ θ b x hθ hx

end OpenTheory.Exact
