import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Order.Filter.Basic

/-!
# The gradient-descent plateau: exact mode dynamics

For a two-layer linear network trained by gradient flow on whitened data from a
balanced initialization of scale `ε` aligned with the singular vectors of the
data, each singular mode evolves on its own: its strength `w` solves
`ẇ = 2 w (σ - w)`, `w(0) = ε²`, where `σ` is the mode's singular value. The
solution is `mode σ ε t = σ / (1 + (σ / ε² - 1) e^{-2σt})` (`mode_zero`,
`hasDerivAt_mode`).

A mode with `σ c > 1` is learned, and a mode with `σ c < 1` is still off, at
time `c · log (1/ε)`, with explicit bounds (`sub_mode_le`, `mode_le`). Hence on
the window `[c₁ log (1/ε), c₂ log (1/ε)]` all signal modes (`σ c₁ > 1`) are
learned and all noise modes (`σ c₂ < 1`) are off, uniformly, as `ε → 0⁺`
(`plateau`). With `W(t) = Σᵢ wᵢ(t) uᵢ vᵢᵀ`, this says `W(t)` is uniformly close to
the best fit keeping exactly the signal modes.
-/

noncomputable section
open Real Filter Topology Set

namespace OpenTheory.Plateau

/-- Strength of one singular mode under gradient flow from balanced initialization `ε`. -/
def mode (σ ε t : ℝ) : ℝ := σ / (1 + (σ / ε ^ 2 - 1) * exp (-2 * σ * t))

variable {σ ε t : ℝ}

theorem coef_pos (hε : 0 < ε) (h : ε ^ 2 < σ) : 0 < σ / ε ^ 2 - 1 := by
  rw [sub_pos, one_lt_div (by positivity)]; exact h

theorem denom_ge_one (hε : 0 < ε) (h : ε ^ 2 < σ) (t : ℝ) :
    1 ≤ 1 + (σ / ε ^ 2 - 1) * exp (-2 * σ * t) := by
  have := coef_pos hε h
  have := exp_pos (-2 * σ * t)
  nlinarith

theorem mode_zero (hε : ε ≠ 0) (hσ : σ ≠ 0) : mode σ ε 0 = ε ^ 2 := by
  simp [mode]
  field_simp

/-- The closed form solves `ẇ = 2 w (σ - w)`. -/
theorem hasDerivAt_mode (hε : 0 < ε) (h : ε ^ 2 < σ) (t : ℝ) :
    HasDerivAt (mode σ ε) (2 * mode σ ε t * (σ - mode σ ε t)) t := by
  set K := σ / ε ^ 2 - 1
  have hD : HasDerivAt (fun t => 1 + K * exp (-2 * σ * t))
      (K * (exp (-2 * σ * t) * (-2 * σ))) t := by
    have := ((hasDerivAt_id t).const_mul (-2 * σ)).exp
    simpa [mul_comm] using (this.const_mul K).const_add 1
  have hne : 1 + K * exp (-2 * σ * t) ≠ 0 := (lt_of_lt_of_le one_pos (denom_ge_one hε h t)).ne'
  have := HasDerivAt.div (hasDerivAt_const t σ) hD hne
  have hf : mode σ ε = fun y => σ / (1 + K * exp (-2 * σ * y)) := rfl
  have hv : 2 * mode σ ε t * (σ - mode σ ε t) =
      (0 * (1 + K * exp (-2 * σ * t)) - σ * (K * (exp (-2 * σ * t) * (-2 * σ)))) /
        (1 + K * exp (-2 * σ * t)) ^ 2 := by
    show 2 * (σ / (1 + K * exp (-2 * σ * t))) * (σ - σ / (1 + K * exp (-2 * σ * t))) = _
    generalize exp (-2 * σ * t) = e at hne ⊢
    field_simp
    ring
  rw [hv, hf]
  exact this

/-- A learned mode: `0 ≤ σ - w(t) ≤ σ (σ/ε²) e^{-2σt}`. -/
theorem sub_mode_le (hε : 0 < ε) (h : ε ^ 2 < σ) (t : ℝ) :
    0 ≤ σ - mode σ ε t ∧ σ - mode σ ε t ≤ σ * (σ / ε ^ 2) * exp (-2 * σ * t) := by
  have hσ : 0 < σ := lt_of_le_of_lt (by positivity) h
  have hK := coef_pos hε h
  have hD := denom_ge_one hε h t
  have he := exp_pos (-2 * σ * t)
  set D := 1 + (σ / ε ^ 2 - 1) * exp (-2 * σ * t) with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD
  have hsub : σ - mode σ ε t = σ * (D - 1) / D := by
    simp only [mode, ← hDdef]; field_simp
  rw [hsub]
  refine ⟨by apply div_nonneg <;> nlinarith, ?_⟩
  rw [div_le_iff₀ hDpos]
  have h1 : D - 1 = (σ / ε ^ 2 - 1) * exp (-2 * σ * t) := by rw [hDdef]; ring
  have h2 : (σ / ε ^ 2 - 1) * exp (-2 * σ * t) ≤ σ / ε ^ 2 * exp (-2 * σ * t) := by nlinarith
  have h3 : 0 ≤ σ / ε ^ 2 * exp (-2 * σ * t) := by positivity
  have h4 : D - 1 ≤ σ / ε ^ 2 * exp (-2 * σ * t) := h1 ▸ h2
  nlinarith [mul_le_mul_of_nonneg_left h4 hσ.le,
    mul_le_mul_of_nonneg_left hD (mul_nonneg hσ.le h3)]

/-- A mode still off: `0 ≤ w(t) ≤ σ / ((σ/ε² - 1) e^{-2σt})`. -/
theorem mode_le (hε : 0 < ε) (h : ε ^ 2 < σ) (t : ℝ) :
    0 ≤ mode σ ε t ∧ mode σ ε t ≤ σ / ((σ / ε ^ 2 - 1) * exp (-2 * σ * t)) := by
  have hσ : 0 < σ := lt_of_le_of_lt (by positivity) h
  have hK := coef_pos hε h
  have hD := denom_ge_one hε h t
  have he := exp_pos (-2 * σ * t)
  refine ⟨div_nonneg hσ.le (by linarith), ?_⟩
  exact div_le_div_of_nonneg_left hσ.le (by positivity) (by linarith)

/-! ### The plateau window -/

theorem exp_mul_log_inv (hε : 0 < ε) (a : ℝ) : exp (-a * log (1 / ε)) = ε ^ a := by
  rw [one_div, log_inv, rpow_def_of_pos hε]; ring_nf

/-- **Signal modes are learned.** If `σ c₁ > 1`, then `w(t) → σ` uniformly on
`t ≥ c₁ log (1/ε)` as `ε → 0⁺`. -/
theorem signal_learned (hσ : 0 < σ) {c₁ : ℝ} (hc : 1 < σ * c₁) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, c₁ * log (1 / ε) ≤ t → |σ - mode σ ε t| < δ := by
  -- the bound σ² ε^{2σc₁ - 2} tends to 0
  have hp : 0 < 2 * σ * c₁ - 2 := by linarith
  have hlim : Tendsto (fun ε : ℝ => σ ^ 2 * ε ^ (2 * σ * c₁ - 2)) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [zero_rpow hp.ne'] using this.const_mul (σ ^ 2)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 < σ ∧ ε < 1 := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ^ 2 < σ := by
      have : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
      exact this.eventually (gt_mem_nhds (by simpa using hσ))
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := gt_mem_nhds one_pos
    exact (h1.and h2).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, hlim.eventually (gt_mem_nhds hδ), self_mem_nhdsWithin] with
    ε ⟨hεσ, hε1⟩ hbound (hε : 0 < ε) t ht
  obtain ⟨h0, hle⟩ := sub_mode_le hε hεσ t
  rw [abs_of_nonneg h0]
  refine lt_of_le_of_lt (hle.trans ?_) hbound
  -- e^{-2σt} ≤ e^{-2σ c₁ log(1/ε)} = ε^{2σc₁}
  have hlog : 0 ≤ log (1 / ε) := log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hexp : exp (-2 * σ * t) ≤ ε ^ (2 * σ * c₁) := by
    rw [← exp_mul_log_inv hε]
    exact exp_le_exp.2 (by nlinarith)
  have hpow : ε ^ (2 * σ * c₁ - 2) = ε ^ (2 * σ * c₁) / ε ^ 2 := by
    rw [rpow_sub hε, rpow_two]
  rw [hpow]
  calc σ * (σ / ε ^ 2) * exp (-2 * σ * t) ≤ σ * (σ / ε ^ 2) * ε ^ (2 * σ * c₁) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = σ ^ 2 * (ε ^ (2 * σ * c₁) / ε ^ 2) := by ring

/-- **Noise modes are still off.** If `σ c₂ < 1`, then `w(t) → 0` uniformly on
`0 ≤ t ≤ c₂ log (1/ε)` as `ε → 0⁺`. -/
theorem noise_off (hσ : 0 < σ) {c₂ : ℝ} (hc : σ * c₂ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t, t ≤ c₂ * log (1 / ε) → |mode σ ε t| < δ := by
  have hp : 0 < 2 - 2 * σ * c₂ := by linarith
  -- the bound 2 ε^{2 - 2σc₂} (valid once ε² ≤ σ/2) tends to 0
  have hlim : Tendsto (fun ε : ℝ => 2 * ε ^ (2 - 2 * σ * c₂)) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [zero_rpow hp.ne'] using this.const_mul 2
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 < σ / 2 := by
    have : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
    exact (this.eventually (gt_mem_nhds (by simpa using half_pos hσ))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsmall, hlim.eventually (gt_mem_nhds hδ), self_mem_nhdsWithin] with
    ε hεσ hbound (hε : 0 < ε) t ht
  have hεσ' : ε ^ 2 < σ := by linarith
  obtain ⟨h0, hle⟩ := mode_le hε hεσ' t
  rw [abs_of_nonneg h0]
  refine lt_of_le_of_lt (hle.trans ?_) hbound
  have hε2 : 0 < ε ^ 2 := by positivity
  have hK : σ / 2 / ε ^ 2 ≤ σ / ε ^ 2 - 1 := by
    rw [le_sub_iff_add_le, div_add_one hε2.ne', div_le_div_iff_of_pos_right hε2]; linarith
  have hexp : ε ^ (2 * σ * c₂) ≤ exp (-2 * σ * t) := by
    rw [← exp_mul_log_inv hε]; exact exp_le_exp.2 (by nlinarith)
  have hpos : 0 < ε ^ (2 * σ * c₂) := rpow_pos_of_pos hε _
  calc σ / ((σ / ε ^ 2 - 1) * exp (-2 * σ * t)) ≤ σ / (σ / 2 / ε ^ 2 * ε ^ (2 * σ * c₂)) := by
        apply div_le_div_of_nonneg_left hσ.le (by positivity)
        exact mul_le_mul hK hexp hpos.le (by linarith [coef_pos hε hεσ'])
    _ = 2 * ε ^ (2 - 2 * σ * c₂) := by
        rw [rpow_sub hε, rpow_two]; field_simp

/-- **The plateau.** Finitely many modes with singular values `σ i > 0`. On the
window `[c₁ log (1/ε), c₂ log (1/ε)]`, every signal mode (`σ i c₁ > 1`) is within
`δ` of its singular value and every noise mode (`σ i c₂ < 1`) is within `δ` of
zero, for all small enough `ε`. -/
theorem plateau {ι : Type*} [Finite ι] {σ : ι → ℝ} (hσ : ∀ i, 0 < σ i) {c₁ c₂ : ℝ}
    (signal : ι → Prop) (hsig : ∀ i, signal i → 1 < σ i * c₁)
    (hnoise : ∀ i, ¬ signal i → σ i * c₂ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)), ∀ i,
      (signal i → |σ i - mode (σ i) ε t| < δ) ∧ (¬ signal i → |mode (σ i) ε t| < δ) := by
  have hall : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)),
      (signal i → |σ i - mode (σ i) ε t| < δ) ∧ (¬ signal i → |mode (σ i) ε t| < δ) := by
    intro i
    by_cases hs : signal i
    · filter_upwards [signal_learned (hσ i) (hsig i hs) hδ] with ε hε t ht
      exact ⟨fun _ => hε t ht.1, fun h => (h hs).elim⟩
    · filter_upwards [noise_off (hσ i) (hnoise i hs) hδ] with ε hε t ht
      exact ⟨fun h => (hs h).elim, fun _ => hε t ht.2⟩
  filter_upwards [Filter.eventually_all.2 hall] with ε hε t ht i
  exact hε i t ht

end OpenTheory.Plateau
