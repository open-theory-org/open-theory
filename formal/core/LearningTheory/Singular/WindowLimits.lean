import LearningTheory.Singular.PlateauModes
import LearningTheory.Singular.Riccati
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform limits on the window `t ∈ [c₁, c₂] · log(1/ε)`

Three scalar estimates used for the balanced-initialization plateau, all uniform in `t` as
`ε → 0⁺`:

* `amp_small`: if `λ c₂ < 1`, then `ε e^{λt} → 0` for `0 ≤ t ≤ c₂ log(1/ε)`;
* `weight_small`: if `λ c₂ < 1`, then `ε² φ(λ, t) → 0` there;
* `signal_ratio`: if `λ c₁ > 1`, then for `t ≥ c₁ log(1/ε)`, `e^{2λt}/φ(λ,t) → 2λ` (and stays
  `≤ 4λ`), while `e^{λt}/(ε φ(λ,t)) → 0`.
-/

noncomputable section
open Real Filter Topology Set

namespace OpenTheory.Riccati

open OpenTheory.Plateau (exp_mul_log_inv)

theorem eventually_rpow_lt {p η : ℝ} (hp : 0 < p) (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ p < η := by
  have := ((continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  rw [zero_rpow hp.ne'] at this
  exact this.eventually (gt_mem_nhds hη)

theorem eventually_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε using hε

theorem log_inv_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 ≤ log (1 / ε) :=
  log_nonneg (by rw [le_div_iff₀ h0]; linarith)

/-- `e^{a log(1/ε)} = ε^{-a}`. -/
theorem exp_mul_log_inv' {ε : ℝ} (hε : 0 < ε) (a : ℝ) : exp (a * log (1 / ε)) = ε ^ (-a) := by
  rw [← exp_mul_log_inv hε]; ring_nf

theorem amp_small {l c₂ : ℝ} (h : l * c₂ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, 0 ≤ t → t ≤ c₂ * log (1 / ε) → ε * exp (l * t) < η := by
  set m := max l 0
  have hm : m * c₂ < 1 := by
    rcases le_total l 0 with hl | hl
    · simp [m, max_eq_right hl]
    · simpa [m, max_eq_left hl] using h
  have hp : 0 < 1 - m * c₂ := by linarith
  filter_upwards [eventually_rpow_lt hp hη, eventually_small] with ε hε ⟨h0, h1⟩ t ht0 ht
  have hlog := log_inv_nonneg h0 h1
  have hm0 : 0 ≤ m := le_max_right _ _
  calc ε * exp (l * t) ≤ ε * exp (m * c₂ * log (1 / ε)) := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) h0.le
        calc l * t ≤ m * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
          _ ≤ m * (c₂ * log (1 / ε)) := mul_le_mul_of_nonneg_left ht hm0
          _ = m * c₂ * log (1 / ε) := by ring
    _ = ε ^ (1 - m * c₂) := by
        rw [exp_mul_log_inv' h0, rpow_sub h0, rpow_one, rpow_neg h0.le]; field_simp
    _ < η := hε

theorem phi_le (l t : ℝ) : phi l t ≤ t * exp (2 * max l 0 * t) := by
  unfold phi
  split_ifs with hl
  · subst hl; simp
  · rcases lt_or_gt_of_ne hl with hl | hl
    · rw [max_eq_right hl.le, mul_zero, zero_mul, exp_zero, mul_one]
      rw [div_le_iff_of_neg (by linarith)]
      have := add_one_le_exp (2 * l * t)
      nlinarith
    · rw [max_eq_left hl.le, div_le_iff₀ (by linarith)]
      have h1 := add_one_le_exp (-(2 * l * t))
      have h2 : exp (-(2 * l * t)) * exp (2 * l * t) = 1 := by rw [← exp_add]; simp
      have h3 : 0 < exp (2 * l * t) := exp_pos _
      nlinarith

theorem weight_small {l c₂ : ℝ} (h : l * c₂ < 1) (hc₂ : 0 ≤ c₂) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, 0 ≤ t → t ≤ c₂ * log (1 / ε) → ε ^ 2 * phi l t < η := by
  set m := max l 0
  have hm : m * c₂ < 1 := by
    rcases le_total l 0 with hl | hl
    · simp [m, max_eq_right hl]
    · simpa [m, max_eq_left hl] using h
  have hm0 : 0 ≤ m := le_max_right _ _
  set q := 2 - 2 * m * c₂
  have hq : 0 < q := by simp only [q]; linarith
  have hlim := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hpos : 0 < η / (c₂ + 1) := div_pos hη (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |log ε * ε ^ q| < η / (c₂ + 1) :=
    (hlim.eventually (Metric.ball_mem_nhds 0 hpos)).mono fun ε hε => by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  filter_upwards [hev, eventually_small] with ε hε ⟨h0, h1⟩ t ht0 ht
  have hlog := log_inv_nonneg h0 h1
  have hlogε : log (1 / ε) = -log ε := by rw [one_div, log_inv]
  have hphi := phi_le l t
  have hexp : exp (2 * m * t) ≤ ε ^ (-(2 * m * c₂)) := by
    rw [← exp_mul_log_inv' h0]
    exact exp_le_exp.2 (by nlinarith)
  have key : ε ^ 2 * phi l t ≤ c₂ * (-log ε * ε ^ q) := by
    calc ε ^ 2 * phi l t ≤ ε ^ 2 * (t * exp (2 * m * t)) :=
          mul_le_mul_of_nonneg_left hphi (by positivity)
      _ ≤ ε ^ 2 * (c₂ * log (1 / ε) * ε ^ (-(2 * m * c₂))) := by
          gcongr
      _ = c₂ * (-log ε * ε ^ q) := by
          rw [hlogε]
          have : ε ^ q = ε ^ (2 : ℝ) * ε ^ (-(2 * m * c₂)) := by
            rw [← rpow_add h0]; simp only [q]; ring_nf
          rw [this, rpow_two]; ring
  have hb : -log ε * ε ^ q < η / (c₂ + 1) := by
    have := (abs_lt.1 hε).1; linarith
  have h1' : c₂ * (-log ε * ε ^ q) ≤ c₂ * (η / (c₂ + 1)) := mul_le_mul_of_nonneg_left hb.le hc₂
  have h2' : c₂ * (η / (c₂ + 1)) < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

theorem signal_ratio {l c₁ : ℝ} (hl : 0 < l) (h : 1 < l * c₁) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, c₁ * log (1 / ε) ≤ t →
      |exp (2 * l * t) / phi l t - 2 * l| < η ∧ exp (2 * l * t) / phi l t ≤ 4 * l ∧
        exp (l * t) / (ε * phi l t) < η := by
  have hc₁ : 0 < c₁ := by
    by_contra hc; push Not at hc; nlinarith
  have hp1 : 0 < 2 * l * c₁ := by positivity
  have hp2 : 0 < l * c₁ - 1 := by linarith
  have h4l : 0 < η / (4 * l) := by positivity
  have hη1 : 0 < min (1 / 2) (η / (4 * l)) := lt_min (by norm_num) h4l
  filter_upwards [eventually_rpow_lt hp1 hη1, eventually_rpow_lt hp2 h4l, eventually_small] with
    ε hx hy ⟨h0, h1⟩ t ht
  have hlog := log_inv_nonneg h0 h1
  set F := exp (l * t)
  have hF : 0 < F := exp_pos _
  have hEF : exp (2 * l * t) = F * F := by simp only [F]; rw [← exp_add]; ring_nf
  have hFinv : F⁻¹ ≤ ε ^ (l * c₁) := by
    rw [← exp_neg, ← exp_mul_log_inv h0]; exact exp_le_exp.2 (by nlinarith)
  have hxle : (F * F)⁻¹ ≤ ε ^ (2 * l * c₁) := by
    rw [← hEF, ← exp_neg, ← exp_mul_log_inv h0]; exact exp_le_exp.2 (by nlinarith)
  set x := (F * F)⁻¹
  have hxs : x < min (1 / 2) (η / (4 * l)) := lt_of_le_of_lt hxle hx
  have hx12 : x < 1 / 2 := lt_of_lt_of_le hxs (min_le_left _ _)
  have hxη : x < η / (4 * l) := lt_of_lt_of_le hxs (min_le_right _ _)
  have hx0 : 0 < x := by positivity
  have hFF : 2 < F * F := by
    have : (F * F)⁻¹ < 2⁻¹ := by rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; exact hx12
    exact (inv_lt_inv₀ (by positivity) (by positivity)).1 this
  have hphi : phi l t = (F * F - 1) / (2 * l) := by
    unfold phi; rw [ite_eq_right hl.ne', hEF]
  have hratio : exp (2 * l * t) / phi l t = 2 * l / (1 - x) := by
    rw [hEF, hphi]
    have h1 : F * F - 1 ≠ 0 := by linarith
    have h2 : F ^ 2 - 1 ≠ 0 := by rw [sq]; exact h1
    have : 1 - x ≠ 0 := by linarith
    field_simp
    simp only [x]
    field_simp
  have h4lx : 4 * l * x < η := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * l)).1 hxη; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hratio]
    have e : 2 * l / (1 - x) - 2 * l = 2 * l * x / (1 - x) := by
      have : 1 - x ≠ 0 := by linarith
      field_simp; ring
    rw [e, abs_of_nonneg (by apply div_nonneg <;> nlinarith), div_lt_iff₀ (by linarith)]
    nlinarith
  · rw [hratio, div_le_iff₀ (by linarith)]; nlinarith
  · have hεF : 4 * l * F⁻¹ < η * ε := by
      have hεp : ε ^ (l * c₁) = ε * ε ^ (l * c₁ - 1) := by
        rw [← rpow_one_add' h0.le (by linarith)]; ring_nf
      calc 4 * l * F⁻¹ ≤ 4 * l * (ε * ε ^ (l * c₁ - 1)) := by
            rw [← hεp]; exact mul_le_mul_of_nonneg_left hFinv (by positivity)
        _ < 4 * l * (ε * (η / (4 * l))) := by gcongr
        _ = η * ε := by field_simp
    have hkey : 4 * l < η * ε * F := by
      have := mul_lt_mul_of_pos_right hεF hF
      rwa [mul_assoc, inv_mul_cancel₀ hF.ne', mul_one] at this
    rw [hphi, div_lt_iff₀ (by apply mul_pos h0; apply div_pos <;> linarith)]
    rw [show η * (ε * ((F * F - 1) / (2 * l))) = η * ε * (F * F - 1) / (2 * l) by ring,
      lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos hη h0) hF]

end OpenTheory.Riccati
