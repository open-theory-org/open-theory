import Specs.Basic
import Scopes.LinearRegion

/-!
# Linear and logistic-regression models on a region as specifications

The two checks of `Checks/Linear.lean` as instances of `Sound` with no randomness and `δ = 0`,
for the same specifications as the tree checks (`robust-decision`, `monotone-feature`).
-/

open MeasureTheory

namespace OpenTheory

open Checks.Linear Checks.Tree

/-- **`robust-decision`** (linear models). For every box `B` and decision `c` the kernel accepts
(`robustK`, what `ot_kernel` evaluates),
the model decides `c` on every real input of `B`. -/
theorem linearRobust_sound (m : LinearModel) :
    Sound (Measure.dirac ())
      (fun _ (θ : Box × Bool) => Checks.Linear.robustK m.bias m.τ m.weights θ.1 θ.2 = true)
      (fun θ => (⟨.property (Decides θ.2), .region {x | θ.1.Mem x}, .all⟩ :
        Spec LinearModel (ℕ → ℝ)).Target m) 0 := by
  rw [sound_exact_iff]
  rintro ⟨B, c⟩ h
  rw [Checks.Linear.robustK_eq] at h
  exact fun x hx => Checks.Linear.robust_sound m B c h x hx

/-- **`monotone-feature`** (linear models). If the weight of feature `j` has the sign the check
asks for, raising feature `j` (the others fixed) moves the score in that direction, on any box. -/
theorem linearMonotone_sound (m : LinearModel) :
    Sound (Measure.dirac ())
      (fun _ (θ : Box × ℕ × Bool) => Checks.Linear.monotone m.weights θ.2.1 θ.2.2 = true)
      (fun θ => (⟨.property (MonotoneIn θ.2.1 θ.2.2), .region {xx | θ.1.Mem xx.1 ∧ θ.1.Mem xx.2}, .all⟩ :
        Spec LinearModel ((ℕ → ℝ) × (ℕ → ℝ))).Target m) 0 := by
  rw [sound_exact_iff]
  rintro ⟨B, j, up⟩ h
  exact fun xx _ hr => Checks.Linear.monotone_sound m j up h hr

end OpenTheory
