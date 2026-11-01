import Properties.Basic

/-!
# What a model family provides, and the properties stated once for all of them

A property is about a model through what the model does, not through how it is built. A family
says what it does by instances of two classes:

| Class | A model `m` of the family … | Families |
| --- | --- | --- |
| `HasDecision M X Y` | decides `y` on input `x` (`Decision m x y`) | tree ensembles (approve or not), ReLU networks (the predicted class) |
| `HasScore M X` | gives a real score on `x` | tree ensembles |

The properties below are written once against these classes, so each holds the same meaning for
every family, and a claim type for a new family reuses its property card as it is. See
`docs/language.md`.
-/

namespace OpenTheory

/-- A family whose models decide: `Decision m x y` says the model `m` decides `y` on `x`. -/
class HasDecision (M X Y : Type*) where
  Decision : M → X → Y → Prop

/-- A family whose models give a real score on each input. -/
class HasScore (M X : Type*) where
  score : M → X → ℝ

/-- **`decision`.** The model's decision on `x` is `y`. -/
def Decides {M X Y : Type*} [HasDecision M X Y] (y : Y) : Property M X :=
  fun m x => HasDecision.Decision m x y

/-- The order a monotonicity claim asks for: `a ≤ b` if increasing, `b ≤ a` if decreasing. -/
def Ordered (up : Bool) (a b : ℝ) : Prop := if up then a ≤ b else b ≤ a

/-- Two feature vectors that differ only in feature `j`, the second at least the first there. -/
def Raised (j : ℕ) (x x' : ℕ → ℝ) : Prop := (∀ i, i ≠ j → x i = x' i) ∧ x j ≤ x' j

/-- **`monotone`.** On a pair `(x, x')` where `x'` raises feature `j` of `x`, the score moves in
the stated direction (up if `up`). -/
def MonotoneIn {M : Type*} [HasScore M (ℕ → ℝ)] (j : ℕ) (up : Bool) : Property M ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun m xx => Raised j xx.1 xx.2 → Ordered up (HasScore.score m xx.1) (HasScore.score m xx.2)

end OpenTheory
