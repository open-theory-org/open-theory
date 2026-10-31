import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Domains, aggregates and the guarantee of a certificate

A domain says which inputs a specification is about: a region, a committed pool, a distribution
(known only through an assumption), or a pair of these. An aggregate says what it asks of them:
the observable holds everywhere, its mean (a rate, for a property) is at most or at least a bound,
a quantile is at most a bound, or, on a pair, the two means differ by at most `ε` or have a ratio
at least `c`.

`Sound` is the one guarantee every certificate gives: over the randomness of how the evidence was
collected, the probability that the check accepts a false claim is at most `δ`, uniformly over the
parameters chosen after seeing the evidence. With no randomness, `δ = 0` (`sound_exact_iff`). See
`docs/specs.md`.
-/

open MeasureTheory

namespace OpenTheory

/-- Which inputs a specification is about. -/
inductive Domain (X : Type*) where
  /-- every input of the set `R` -/
  | region (R : Set X)
  /-- a committed pool of `N` items, each with weight `1/N` -/
  | pool (N : ℕ) (item : Fin N → X)
  /-- a distribution `D` (with its own σ-algebra), known only through an assumption -/
  | distribution (σ : MeasurableSpace X) (D : @Measure X σ)
  /-- two domains, compared by `gapLe` and `ratioGe` -/
  | pair (d₁ d₂ : Domain X)

/-- What a specification asks of its domain. For a property, the mean is the rate. -/
inductive Aggregate where
  /-- the observable holds on every input -/
  | all
  /-- the mean is at most `a` (for a property: the rate is at most `a`) -/
  | meanLe (a : ℝ)
  /-- the mean is at least `a` -/
  | meanGe (a : ℝ)
  /-- the `α`-quantile is at most `t`: the value exceeds `t` on at most a fraction `1 - α` -/
  | quantileLe (α t : ℝ)
  /-- on a pair: the two means differ by at most `ε` -/
  | gapLe (ε : ℝ)
  /-- on a pair: the first mean is at least `c` times the second -/
  | ratioGe (c : ℝ)

/-- The predicate `H` holds on every input of the domain (almost every, for a distribution). -/
def Domain.All {X : Type*} : Domain X → (X → Prop) → Prop
  | .region R, H => ∀ x ∈ R, H x
  | .pool _ item, H => ∀ j, H (item j)
  | .distribution σ D, H => ∀ᵐ x ∂(@id (@Measure X σ) D), H x
  | .pair d₁ d₂, H => d₁.All H ∧ d₂.All H

/-- **The guarantee of every certificate.** Over the randomness `ω` of how the evidence was
collected (law `P`), the probability that the check accepts some parameters `θ`, chosen after
seeing `ω` (a count `k`, a bound `p`, …), while the target for `θ` fails, is at most `δ`. -/
def Sound {Ω Θ : Type*} [MeasurableSpace Ω] (P : Measure Ω) (accepts : Ω → Θ → Prop)
    (target : Θ → Prop) (δ : ℝ) : Prop :=
  P {ω | ∃ θ, accepts ω θ ∧ ¬ target θ} ≤ ENNReal.ofReal δ

/-- With no randomness and `δ = 0`, the guarantee is plain implication: exact claims. -/
theorem sound_exact_iff {Θ : Type*} (accepts target : Θ → Prop) :
    Sound (Measure.dirac ()) (fun _ θ => accepts θ) target 0 ↔ ∀ θ, accepts θ → target θ := by
  simp [Sound]

end OpenTheory
