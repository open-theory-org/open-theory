import Specs.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Claim types, and how claims combine

A **claim type** is a specification with its numbers left as parameters, together with how the
evidence is collected, what the check accepts, and the theorem that gives the guarantee:

| Field | Meaning | Example (`tree-robust`) |
| --- | --- | --- |
| `Param` | what a certificate fills in, possibly after seeing the evidence | a box, a decision, one bound per tree |
| `Evidence`, `law` | the randomness of how the evidence is collected | `Unit`, the Dirac measure |
| `accepts` | what the check accepts | the kernel check `robustCertK … = true` |
| `spec`, `model` | the claim a parameter stands for | decision `c` on every input of the box |
| `δ`, `sound` | the guarantee, proved once | `Sound law accepts … 0` |

A **claim** is a claim type with its parameter: `(T.spec θ).Target (T.model θ)`. Every card of
`specs/claims/` names its claim types (`Specs/ClaimTypes.lean`), so the card, the statement and the
proof are one object.

Claims combine by two rules, proved once: `Sound.and` (two checks on the same evidence: the
probability that either accepts a false claim is at most `δ₁ + δ₂`, with no independence needed)
and `Sound.comap` (evidence computed from a larger random draw keeps its guarantee). A report is
a list of claims over one draw, and its `δ` is the sum of theirs.
-/

open MeasureTheory

namespace OpenTheory

universe u v w x

/-- A claim type: a specification with parameters, its evidence, its check and its guarantee. -/
structure ClaimType (M : Type u) (X : Type v) where
  /-- What a certificate fills in, possibly after seeing the evidence. -/
  Param : Type w
  /-- The randomness of how the evidence is collected (`Unit` when there is none). -/
  Evidence : Type x
  [measurable : MeasurableSpace Evidence]
  /-- The law of the evidence. -/
  law : Measure Evidence
  /-- What the check accepts. -/
  accepts : Evidence → Param → Prop
  /-- The specification a parameter stands for. -/
  spec : Param → Spec M X
  /-- The model the claim is about. -/
  model : Param → M
  /-- The probability of accepting a false claim is at most `δ`. -/
  δ : ℝ
  sound : Sound law accepts (fun θ => (spec θ).Target (model θ)) δ

attribute [instance] ClaimType.measurable

/-- The claim a parameter stands for. -/
def ClaimType.Claim {M : Type u} {X : Type v} (T : ClaimType.{u, v, w, x} M X) (θ : T.Param) : Prop :=
  (T.spec θ).Target (T.model θ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Two claims on the same evidence.** The probability that the two checks accept a pair of
parameters of which one claim is false is at most `δ₁ + δ₂` (a union bound: no independence). -/
theorem Sound.and {Θ₁ Θ₂ : Type*} {a₁ : Ω → Θ₁ → Prop} {a₂ : Ω → Θ₂ → Prop}
    {t₁ : Θ₁ → Prop} {t₂ : Θ₂ → Prop} {δ₁ δ₂ : ℝ} (h₁ : Sound P a₁ t₁ δ₁) (h₂ : Sound P a₂ t₂ δ₂)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) :
    Sound P (fun ω (θ : Θ₁ × Θ₂) => a₁ ω θ.1 ∧ a₂ ω θ.2) (fun θ => t₁ θ.1 ∧ t₂ θ.2) (δ₁ + δ₂) := by
  unfold Sound at *
  calc P {ω | ∃ θ : Θ₁ × Θ₂, (a₁ ω θ.1 ∧ a₂ ω θ.2) ∧ ¬(t₁ θ.1 ∧ t₂ θ.2)}
      ≤ P ({ω | ∃ θ, a₁ ω θ ∧ ¬ t₁ θ} ∪ {ω | ∃ θ, a₂ ω θ ∧ ¬ t₂ θ}) := by
        refine measure_mono fun ω ⟨θ, ⟨h1, h2⟩, hn⟩ => ?_
        by_cases ht : t₁ θ.1
        · exact Or.inr ⟨θ.2, h2, fun h => hn ⟨ht, h⟩⟩
        · exact Or.inl ⟨θ.1, h1, ht⟩
    _ ≤ P {ω | ∃ θ, a₁ ω θ ∧ ¬ t₁ θ} + P {ω | ∃ θ, a₂ ω θ ∧ ¬ t₂ θ} := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₂ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (δ₁ + δ₂) := (ENNReal.ofReal_add hδ₁ hδ₂).symm

/-- **Evidence computed from a larger draw.** If the evidence is `f ω'` for a draw `ω'` whose law
`P'` pushes forward to `P`, the guarantee holds over `P'`. -/
theorem Sound.comap {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : Measurable f) (hP : P'.map f = P) {Θ : Type*} {a : Ω → Θ → Prop} {t : Θ → Prop} {δ : ℝ}
    (h : Sound P a t δ) : Sound P' (fun ω' θ => a (f ω') θ) t δ := by
  unfold Sound at *
  set S := {ω | ∃ θ, a ω θ ∧ ¬ t θ}
  calc P' {ω' | ∃ θ, a (f ω') θ ∧ ¬ t θ} = P' (f ⁻¹' S) := rfl
    _ ≤ P' (f ⁻¹' toMeasurable P S) := measure_mono (Set.preimage_mono (subset_toMeasurable P S))
    _ = P (toMeasurable P S) := by
      subst hP; exact (Measure.map_apply hf (measurableSet_toMeasurable _ S)).symm
    _ = P S := measure_toMeasurable S
    _ ≤ ENNReal.ofReal δ := h

end OpenTheory
