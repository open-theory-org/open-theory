import Specs.Basic
import Scopes.TreeRegion

/-!
# Tree ensembles on a region as specifications

The two region checks of `Checks/Tree.lean` as instances of `Sound` (`Specs.Basic`), with no
randomness and `δ = 0`: an accepted claim is true.

| Claim | Observable | Domain | Aggregate |
| --- | --- | --- | --- |
| `robust-decision` | property: the decision is `c` | region (a box) | all |
| `monotone-feature` | property on pairs: raising feature `j` moves the score in the stated direction | region (pairs in a box) | all |
-/

open MeasureTheory

namespace OpenTheory

open Checks.Tree

/-- **`robust-decision`** (trees). For every box `B`, decision `c` and per-tree bounds `ms` the kernel accepts
(`robustCertK`, what `ot_kernel` evaluates), the ensemble's decision is `c` on every real input of
`B`. -/
theorem treeRobust_sound (e : Ensemble) :
    Sound (Measure.dirac ())
      (fun _ (θ : Box × Bool × List Int) => robustCertK e.base e.τ e.trees θ.2.2 θ.1 θ.2.1 = true)
      (fun θ => (⟨.property fun e x => (e.Approves x ↔ θ.2.1 = true), .region {x | θ.1.Mem x}, .all⟩ :
        Spec Ensemble (ℕ → ℝ)).Target e) 0 := by
  rw [sound_exact_iff]
  rintro ⟨B, c, ms⟩ h
  rw [robustCertK_eq] at h
  exact fun x hx => robustCert_sound e ms B c h x hx

/-- **`monotone-feature`** (trees). For every box `B`, feature `j`, direction and cuts the kernel accepts
(`monotoneCertK`), raising feature `j` of an input of `B` (within `B`, the other features fixed)
never lowers the ensemble's score if `up`, never raises it otherwise. -/
theorem treeMonotone_sound (e : Ensemble) :
    Sound (Measure.dirac ())
      (fun _ (θ : Box × ℕ × Bool × List Cuts) => monotoneCertK θ.2.1 θ.2.2.1 e.trees θ.1 θ.2.2.2 = true)
      (fun θ => (⟨.property fun e (xx : (ℕ → ℝ) × (ℕ → ℝ)) =>
          Raised θ.2.1 xx.1 xx.2 → Ordered θ.2.2.1 (e.score xx.1) (e.score xx.2),
        .region {xx | θ.1.Mem xx.1 ∧ θ.1.Mem xx.2}, .all⟩ :
          Spec Ensemble ((ℕ → ℝ) × (ℕ → ℝ))).Target e) 0 := by
  rw [sound_exact_iff]
  rintro ⟨B, j, up, cs⟩ h
  rw [monotoneCertK_eq] at h
  exact fun xx hxx hr => monotoneCert_sound e j up cs B h hxx.1 hxx.2 hr

end OpenTheory
