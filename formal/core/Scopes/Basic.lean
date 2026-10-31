import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Scopes and the guarantee of a certificate

A scope says where a property must hold: on every input of a region, or on all but a fraction `p`
of a population. `Sound` is the one guarantee every certificate gives, whatever its scope: over the
randomness of how the evidence was collected, the probability that the check accepts a false claim
is at most `δ`. The claim's parameters (a count, a bound, a box) may be chosen after seeing the
evidence. For a region scope there is no randomness and `δ = 0` (`sound_exact_iff`). See
`docs/specs.md`.
-/

open MeasureTheory

namespace OpenTheory

/-- Where a property must hold. -/
inductive Scope (X : Type*) where
  /-- on every input of the region `R` (a finite list of inputs is a region too) -/
  | region (R : Set X)
  /-- on all but a fraction `p` of the population the evidence was sampled from -/
  | population (p : ℝ)

/-- **The guarantee of every certificate.** Over the randomness `ω` of how the evidence was
collected (law `P`), the probability that the check accepts some parameters `θ`, chosen after
seeing `ω` (a count `k`, a bound `p`, …), while the target for `θ` fails, is at most `δ`. -/
def Sound {Ω Θ : Type*} [MeasurableSpace Ω] (P : Measure Ω) (accepts : Ω → Θ → Prop)
    (target : Θ → Prop) (δ : ℝ) : Prop :=
  P {ω | ∃ θ, accepts ω θ ∧ ¬ target θ} ≤ ENNReal.ofReal δ

/-- With no randomness and `δ = 0`, the guarantee is plain implication: exact scopes. -/
theorem sound_exact_iff {Θ : Type*} (accepts target : Θ → Prop) :
    Sound (Measure.dirac ()) (fun _ θ => accepts θ) target 0 ↔ ∀ θ, accepts θ → target θ := by
  simp [Sound]

end OpenTheory
