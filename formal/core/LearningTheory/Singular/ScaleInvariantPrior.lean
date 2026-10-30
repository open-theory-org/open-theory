import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Bayes generalization for a scale-invariant prior: `E[m(z)²] = α`

Observe `z ~ N(u, 1)` with the (improper) prior `|u|^{α-1} du`, `α > 0`. The
posterior mean is `m(z) = ∫ u w(z,u) du / ∫ w(z,u) du` with weight
`w(z,u) = |u|^{α-1} e^{-(z-u)²/2}`. Under the truth `u = 0`, `z ~ N(0,1)`, and

  `E[m(z)²] = α`.

This is the local form of the Bayes generalization error for the singular toy
models `y = a·bᵏ·x` (with `α = 1/k`): the Bayes coefficient is `α/2`, the learning
coefficient `λ`.

Proof: with `q = ∫ w`, `q' = ∫ (u-z) w`, `q'' = ∫ ((u-z)² - 1) w`, integration by
parts in `u` gives `q'' + z q' = (α - 1) q`. With `L = log q`, `m = z + L'` and
`L'² = (α - 1) - z L' - L''`; Gaussian integration by parts gives
`E[L''] = E[z L']`, hence `E[m²] = α`.

This file: integrability foundations.
-/

noncomputable section
open Real MeasureTheory Filter Topology Set

namespace OpenTheory.BayesToy

/-! ### Integrability of `|u|^s e^{-b u²}` -/

theorem integrable_abs_rpow_mul_exp {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    Integrable (fun u : ℝ => |u| ^ s * exp (-b * u ^ 2)) := by
  set g : ℝ → ℝ := fun u => |u| ^ s * exp (-b * u ^ 2)
  have hpos : IntegrableOn g (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp [g, abs_of_pos (mem_Ioi.mp hu)]
  have h1 : Integrable ((Ioi (0 : ℝ)).indicator g) := hpos.integrable_indicator measurableSet_Ioi
  have h2 : Integrable (fun u => (Ioi (0 : ℝ)).indicator g (-u)) := h1.comp_neg
  refine (h1.add h2).congr ?_
  have hae : ∀ᵐ u : ℝ, u ∉ ({0} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
  filter_upwards [hae] with u hu
  have hu : u ≠ 0 := by simpa using hu
  show (Ioi (0 : ℝ)).indicator g u + (Ioi (0 : ℝ)).indicator g (-u) = g u
  rcases lt_or_gt_of_ne hu with h | h
  · rw [Set.indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from not_lt.2 h.le),
      Set.indicator_of_mem (show -u ∈ Ioi (0 : ℝ) from neg_pos.2 h)]
    simp [g, abs_neg]
  · rw [Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from h),
      Set.indicator_of_notMem (show -u ∉ Ioi (0 : ℝ) from by simp; linarith)]
    simp

/-! ### Gaussian domination -/

theorem exp_shift_le {z u R : ℝ} (hz : |z| ≤ R) :
    exp (-((z - u) ^ 2 / 2)) ≤ exp (R ^ 2 / 2) * exp (-(1 / 4) * u ^ 2) := by
  rw [← exp_add]
  apply exp_le_exp.2
  have hz2 : z ^ 2 ≤ R ^ 2 := by
    have := abs_nonneg z
    nlinarith [sq_abs z]
  nlinarith [sq_nonneg (u - 2 * z)]

/-- The posterior weight `|u|^{α-1} e^{-(z-u)²/2}`. -/
def w (α z u : ℝ) : ℝ := |u| ^ (α - 1) * exp (-((z - u) ^ 2 / 2))

theorem w_nonneg (α z u : ℝ) : 0 ≤ w α z u := by unfold w; positivity

/-- A single integrable function dominating `(1 + |u|)^k w(z,u)`, `k ≤ 2`, uniformly in `|z| ≤ R`. -/
def dom (α R u : ℝ) : ℝ :=
  exp (R ^ 2 / 2) * (|u| ^ (α - 1) + |u| ^ α + |u| ^ (α + 1)) * exp (-(1 / 4) * u ^ 2)

theorem dom_integrable {α : ℝ} (hα : 0 < α) (R : ℝ) : Integrable (dom α R) := by
  have h0 := integrable_abs_rpow_mul_exp (b := 1 / 4) (by norm_num) (s := α - 1) (by linarith)
  have h1 := integrable_abs_rpow_mul_exp (b := 1 / 4) (by norm_num) (s := α) (by linarith)
  have h2 := integrable_abs_rpow_mul_exp (b := 1 / 4) (by norm_num) (s := α + 1) (by linarith)
  refine ((h0.add h1).add h2).const_mul (exp (R ^ 2 / 2)) |>.congr (Eventually.of_forall fun u => ?_)
  simp only [dom, Pi.add_apply]
  ring

/-! ### Powers of `|u|` -/

theorem abs_mul_rpow {α : ℝ} (hα : 0 < α) (u : ℝ) : |u| * |u| ^ (α - 1) = |u| ^ α := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [zero_rpow hα.ne']
  · have hpos : 0 < |u| := abs_pos.2 hu
    rw [mul_comm, ← rpow_add_one hpos.ne', sub_add_cancel]

theorem sq_mul_rpow {α : ℝ} (hα : 0 < α) (u : ℝ) : u ^ 2 * |u| ^ (α - 1) = |u| ^ (α + 1) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [zero_rpow (by linarith : α + 1 ≠ 0)]
  · have hpos : 0 < |u| := abs_pos.2 hu
    rw [← sq_abs, ← rpow_natCast, ← rpow_add hpos]; norm_num; ring_nf

/-! ### The three moments and their bounds -/

/-- `q(z) = ∫ w(z,u) du`, the marginal density up to normalization. -/
def q (α z : ℝ) : ℝ := ∫ u, w α z u
/-- `q'(z) = ∫ (u - z) w(z,u) du`. -/
def q1 (α z : ℝ) : ℝ := ∫ u, (u - z) * w α z u
/-- `q''(z) = ∫ ((u - z)² - 1) w(z,u) du`. -/
def q2 (α z : ℝ) : ℝ := ∫ u, ((u - z) ^ 2 - 1) * w α z u

theorem measurable_w (α z : ℝ) : Measurable (w α z) := by
  unfold w; fun_prop

theorem w_le {α z R : ℝ} (hz : |z| ≤ R) (u : ℝ) :
    w α z u ≤ exp (R ^ 2 / 2) * |u| ^ (α - 1) * exp (-(1 / 4) * u ^ 2) := by
  unfold w
  calc |u| ^ (α - 1) * exp (-((z - u) ^ 2 / 2))
      ≤ |u| ^ (α - 1) * (exp (R ^ 2 / 2) * exp (-(1 / 4) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left (exp_shift_le hz) (by positivity)
    _ = _ := by ring

/-- `(1 + (|u| + R)²) w(z,u) ≤ C(R) · dom(u)` for `|z| ≤ R`. -/
theorem poly_w_le {α z R : ℝ} (hα : 0 < α) (hz : |z| ≤ R) (u : ℝ) :
    (1 + (|u| + R) ^ 2) * w α z u ≤ (3 + 2 * R ^ 2) * dom α R u := by
  have hw := w_le (α := α) hz u
  have hp : (1 + (|u| + R) ^ 2) ≤ (1 + 2 * R ^ 2) + 2 * u ^ 2 := by
    nlinarith [sq_abs u, sq_nonneg (|u| - R), abs_nonneg u]
  have hdom : (1 + 2 * R ^ 2 + 2 * u ^ 2) * (exp (R ^ 2 / 2) * |u| ^ (α - 1) * exp (-(1 / 4) * u ^ 2))
      ≤ (3 + 2 * R ^ 2) * dom α R u := by
    unfold dom
    have e1 : 0 ≤ exp (R ^ 2 / 2) := (exp_pos _).le
    have e2 : 0 ≤ exp (-(1 / 4) * u ^ 2) := (exp_pos _).le
    have a0 : 0 ≤ |u| ^ (α - 1) := by positivity
    have a1 : 0 ≤ |u| ^ α := by positivity
    have a2 : 0 ≤ |u| ^ (α + 1) := by positivity
    have hsq := sq_mul_rpow hα u
    have key : (1 + 2 * R ^ 2 + 2 * u ^ 2) * |u| ^ (α - 1) ≤
        (3 + 2 * R ^ 2) * (|u| ^ (α - 1) + |u| ^ α + |u| ^ (α + 1)) := by nlinarith
    calc (1 + 2 * R ^ 2 + 2 * u ^ 2) * (exp (R ^ 2 / 2) * |u| ^ (α - 1) * exp (-(1 / 4) * u ^ 2))
        = exp (R ^ 2 / 2) * ((1 + 2 * R ^ 2 + 2 * u ^ 2) * |u| ^ (α - 1)) * exp (-(1 / 4) * u ^ 2) := by
          ring
      _ ≤ exp (R ^ 2 / 2) * ((3 + 2 * R ^ 2) * (|u| ^ (α - 1) + |u| ^ α + |u| ^ (α + 1))) *
            exp (-(1 / 4) * u ^ 2) := by gcongr
      _ = _ := by ring
  calc (1 + (|u| + R) ^ 2) * w α z u ≤ (1 + 2 * R ^ 2 + 2 * u ^ 2) *
        (exp (R ^ 2 / 2) * |u| ^ (α - 1) * exp (-(1 / 4) * u ^ 2)) :=
        mul_le_mul hp hw (w_nonneg _ _ _) (by positivity)
    _ ≤ _ := hdom

theorem abs_sub_le_of_abs_le {u z R : ℝ} (hz : |z| ≤ R) : |u - z| ≤ |u| + R :=
  (abs_sub _ _).trans (by linarith)

/-- Integrability of `p(u) w(z,u)` for any `p` with `|p u| ≤ 1 + (|u| + |z|)²`. -/
theorem integrable_poly_w {α : ℝ} (hα : 0 < α) (z : ℝ) {p : ℝ → ℝ} (hp : Measurable p)
    (hpb : ∀ u, |p u| ≤ 1 + (|u| + |z|) ^ 2) : Integrable (fun u => p u * w α z u) := by
  refine ((dom_integrable hα |z|).const_mul (3 + 2 * |z| ^ 2)).mono'
    (hp.mul (measurable_w α z)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (w_nonneg _ _ _)]
  exact (mul_le_mul_of_nonneg_right (hpb u) (w_nonneg _ _ _)).trans
    (poly_w_le hα le_rfl u)

theorem integrable_w {α : ℝ} (hα : 0 < α) (z : ℝ) : Integrable (w α z) := by
  simpa using integrable_poly_w hα z (p := fun _ => 1) measurable_const
    (fun u => by simp; positivity)

theorem integrable_q1 {α : ℝ} (hα : 0 < α) (z : ℝ) : Integrable (fun u => (u - z) * w α z u) :=
  integrable_poly_w hα z (by fun_prop) fun u => by
    have := abs_sub_le_of_abs_le (u := u) (le_refl |z|)
    nlinarith [abs_nonneg (u - z), abs_nonneg u, abs_nonneg z]

theorem integrable_q2 {α : ℝ} (hα : 0 < α) (z : ℝ) :
    Integrable (fun u => ((u - z) ^ 2 - 1) * w α z u) :=
  integrable_poly_w hα z (by fun_prop) fun u => by
    have h := abs_sub_le_of_abs_le (u := u) (le_refl |z|)
    have h2 : (u - z) ^ 2 ≤ (|u| + |z|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u - z)]

/-! ### Derivatives in `z` -/

theorem hasDerivAt_w (α z u : ℝ) : HasDerivAt (fun z => w α z u) ((u - z) * w α z u) z := by
  have h1 : HasDerivAt (fun z => (z - u) ^ 2) (2 * (z - u)) z :=
    (((hasDerivAt_id z).sub_const u).pow 2).congr_deriv (by simp)
  have hg : HasDerivAt (fun z => -((z - u) ^ 2 / 2)) (-(z - u)) z :=
    (h1.div_const 2).neg.congr_deriv (by ring)
  exact (hg.exp.const_mul (|u| ^ (α - 1))).congr_deriv (by simp only [w]; ring)

theorem hasDerivAt_q1_integrand (α z u : ℝ) :
    HasDerivAt (fun z => (u - z) * w α z u) (((u - z) ^ 2 - 1) * w α z u) z :=
  (((hasDerivAt_const z u).sub (hasDerivAt_id z)).mul (hasDerivAt_w α z u)).congr_deriv
    (by simp; ring)

/-- Uniform bound near `z₀` for the derivative of either integrand. -/
theorem deriv_bound {α z₀ x : ℝ} (hα : 0 < α) (hx : x ∈ Metric.ball z₀ 1) (u : ℝ) {p : ℝ → ℝ}
    (hpb : ∀ x, |p x| ≤ 1 + (|u| + |x|) ^ 2) :
    ‖p x * w α x u‖ ≤ (3 + 2 * (|z₀| + 1) ^ 2) * dom α (|z₀| + 1) u := by
  have hxz : |x| ≤ |z₀| + 1 := by
    have := Metric.mem_ball.1 hx
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub x z₀
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (w_nonneg _ _ _)]
  have h1 : |p x| ≤ 1 + (|u| + (|z₀| + 1)) ^ 2 :=
    (hpb x).trans (by gcongr)
  exact (mul_le_mul_of_nonneg_right h1 (w_nonneg _ _ _)).trans
    (poly_w_le hα hxz u)

theorem hasDerivAt_q {α : ℝ} (hα : 0 < α) (z₀ : ℝ) : HasDerivAt (q α) (q1 α z₀) z₀ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z u => w α z u) (F' := fun z u => (u - z) * w α z u)
    (bound := fun u => (3 + 2 * (|z₀| + 1) ^ 2) * dom α (|z₀| + 1) u) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (measurable_w α z).aestronglyMeasurable)
    (integrable_w hα z₀)
    ((measurable_id.sub_const z₀).mul (measurable_w α z₀)).aestronglyMeasurable
    (Eventually.of_forall fun u x hx => deriv_bound hα hx u (p := fun x => u - x) fun x => by
      have := abs_sub_le_of_abs_le (u := u) (le_refl |x|)
      nlinarith [abs_nonneg (u - x), abs_nonneg u, abs_nonneg x])
    (((dom_integrable hα _).const_mul _))
    (Eventually.of_forall fun u x _ => hasDerivAt_w α x u)
  exact this.2

theorem hasDerivAt_q1 {α : ℝ} (hα : 0 < α) (z₀ : ℝ) : HasDerivAt (q1 α) (q2 α z₀) z₀ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z u => (u - z) * w α z u) (F' := fun z u => ((u - z) ^ 2 - 1) * w α z u)
    (bound := fun u => (3 + 2 * (|z₀| + 1) ^ 2) * dom α (|z₀| + 1) u) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => ((measurable_id.sub_const z).mul (measurable_w α z)).aestronglyMeasurable)
    (integrable_q1 hα z₀)
    (((measurable_id.sub_const z₀).pow_const 2 |>.sub_const 1).mul (measurable_w α z₀)).aestronglyMeasurable
    (Eventually.of_forall fun u x hx => deriv_bound hα hx u (p := fun x => (u - x) ^ 2 - 1) fun x => by
      have h := abs_sub_le_of_abs_le (u := u) (le_refl |x|)
      have h2 : (u - x) ^ 2 ≤ (|u| + |x|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u - x)])
    (((dom_integrable hα _).const_mul _))
    (Eventually.of_forall fun u x _ => hasDerivAt_q1_integrand α x u)
  exact this.2

/-! ### The differential equation `q'' + z q' = (α - 1) q` -/

/-- `F(u) = u |u|^{α-1} e^{-(z-u)²/2}`; its integral of `F'` over `ℝ` vanishes. -/
def Fode (α z u : ℝ) : ℝ := u * w α z u

/-- `F'(u) = ((α - 1) - ((u - z)² - 1) - z (u - z)) w(z,u)` for `u ≠ 0`. -/
def Fode' (α z u : ℝ) : ℝ := ((α - 1) - ((u - z) ^ 2 - 1) - z * (u - z)) * w α z u

/-- `d/du (u |u|^{α-1}) = α |u|^{α-1}` away from `0`. -/
theorem hasDerivAt_mul_abs_rpow {α u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v => v * |v| ^ (α - 1)) (α * |u| ^ (α - 1)) u := by
  rcases lt_or_gt_of_ne hu with h | h
  · -- near `u < 0`: `v |v|^{α-1} = -(-v)^α`
    have hev : (fun v => -((-v) ^ α)) =ᶠ[𝓝 u] fun v => v * |v| ^ (α - 1) := by
      filter_upwards [eventually_lt_nhds h] with v hv
      have hpos : 0 < -v := neg_pos.2 hv
      rw [abs_of_neg hv]
      have : (-v) ^ α = (-v) ^ (α - 1) * (-v) := by
        rw [← rpow_add_one hpos.ne', sub_add_cancel]
      rw [this]; ring
    have hd : HasDerivAt (fun v => -((-v) ^ α)) (α * |u| ^ (α - 1)) u := by
      have h1 := (Real.hasDerivAt_rpow_const (p := α) (Or.inl (neg_pos.2 h).ne')).comp u
        (hasDerivAt_neg u)
      exact h1.neg.congr_deriv (by rw [abs_of_neg h]; ring)
    exact hd.congr_of_eventuallyEq hev.symm
  · have hev : (fun v => v ^ α) =ᶠ[𝓝 u] fun v => v * |v| ^ (α - 1) := by
      filter_upwards [eventually_gt_nhds h] with v hv
      rw [abs_of_pos hv, mul_comm, ← rpow_add_one hv.ne', sub_add_cancel]
    have hd : HasDerivAt (fun v => v ^ α) (α * |u| ^ (α - 1)) u := by
      rw [abs_of_pos h]; exact Real.hasDerivAt_rpow_const (Or.inl h.ne')
    exact hd.congr_of_eventuallyEq hev.symm

theorem hasDerivAt_Fode (α z : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (Fode α z) (Fode' α z u) u := by
  have h1 : HasDerivAt (fun v => (z - v) ^ 2) (-(2 * (z - u))) u :=
    (((hasDerivAt_const u z).sub (hasDerivAt_id u)).pow 2).congr_deriv (by simp)
  have hg : HasDerivAt (fun v => -((z - v) ^ 2 / 2)) (z - u) u :=
    (h1.div_const 2).neg.congr_deriv (by ring)
  have hm := (hasDerivAt_mul_abs_rpow (α := α) hu).mul hg.exp
  have hf : Fode α z = fun v => (v * |v| ^ (α - 1)) * exp (-((z - v) ^ 2 / 2)) := by
    funext v; simp only [Fode, w]; ring
  rw [hf]
  exact hm.congr_deriv (by simp only [Fode', w]; ring)

theorem Fode_zero (α z : ℝ) : Fode α z 0 = 0 := by simp [Fode]

theorem continuousAt_Fode_zero {α : ℝ} (hα : 0 < α) (z : ℝ) : ContinuousAt (Fode α z) 0 := by
  rw [ContinuousAt, Fode_zero]
  have hlim : Tendsto (fun v : ℝ => |v| ^ α) (𝓝 0) (𝓝 0) := by
    have := ((continuous_abs.continuousAt (x := (0 : ℝ))).rpow_const (p := α) (Or.inr hα.le))
    simpa [zero_rpow hα.ne'] using this.tendsto
  refine squeeze_zero_norm (fun v => ?_) hlim
  rw [Real.norm_eq_abs, Fode, w, ← mul_assoc, abs_mul, abs_mul,
    abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), abs_mul_rpow hα, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (rpow_nonneg (abs_nonneg _) _)
    (exp_le_one_iff.2 (by nlinarith [sq_nonneg (z - v)]))

theorem integrable_Fode {α : ℝ} (hα : 0 < α) (z : ℝ) : Integrable (Fode α z) :=
  integrable_poly_w hα z (p := id) measurable_id fun u => by
    simp only [id]; nlinarith [abs_nonneg u, abs_nonneg z, le_abs_self u, neg_abs_le u]

theorem Fode'_eq (α z u : ℝ) :
    Fode' α z u = (α - 1) * w α z u - ((u - z) ^ 2 - 1) * w α z u - z * ((u - z) * w α z u) := by
  simp only [Fode']; ring

theorem integrable_Fode' {α : ℝ} (hα : 0 < α) (z : ℝ) : Integrable (Fode' α z) := by
  have := (((integrable_w hα z).const_mul (α - 1)).sub (integrable_q2 hα z)).sub
    ((integrable_q1 hα z).const_mul z)
  exact this.congr (Eventually.of_forall fun u => (Fode'_eq α z u).symm)

/-- `∫ F' = 0`: `F` vanishes at `0` and at `±∞`. -/
theorem integral_Fode' {α : ℝ} (hα : 0 < α) (z : ℝ) : ∫ u, Fode' α z u = 0 := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (Fode α z) (Fode' α z x) x :=
    fun x hx => hasDerivAt_Fode α z (ne_of_gt hx)
  have hd' : ∀ x ∈ Iio (0 : ℝ), HasDerivAt (Fode α z) (Fode' α z x) x :=
    fun x hx => hasDerivAt_Fode α z (ne_of_lt hx)
  have hcont := continuousAt_Fode_zero hα z
  have htop := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd
    (integrable_Fode' hα z).integrableOn (integrable_Fode hα z).integrableOn
  have hbot := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := -1)
    (fun x hx => hasDerivAt_Fode α z (by simp at hx; linarith))
    (integrable_Fode' hα z).integrableOn (integrable_Fode hα z).integrableOn
  have hR := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hd
    (integrable_Fode' hα z).integrableOn htop
  have hL := integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hd'
    (integrable_Fode' hα z).integrableOn hbot
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrable_Fode' hα z).integrableOn
    (integrable_Fode' hα z).integrableOn, hL, hR, Fode_zero]
  ring

/-- **The differential equation** `q'' + z q' = (α - 1) q`. -/
theorem ode {α : ℝ} (hα : 0 < α) (z : ℝ) : q2 α z + z * q1 α z = (α - 1) * q α z := by
  have h := integral_Fode' hα z
  simp_rw [Fode'_eq] at h
  have i1 : Integrable (fun u => (α - 1) * w α z u - ((u - z) ^ 2 - 1) * w α z u) :=
    ((integrable_w hα z).const_mul _).sub (integrable_q2 hα z)
  have i2 : Integrable (fun u => z * ((u - z) * w α z u)) := (integrable_q1 hα z).const_mul z
  have i3 : Integrable (fun u => (α - 1) * w α z u) := (integrable_w hα z).const_mul _
  rw [integral_sub i1 i2, integral_sub i3 (integrable_q2 hα z),
    integral_const_mul, integral_const_mul] at h
  simp only [q, q1, q2]
  linarith

/-! ### Positivity, the log-derivative, and its growth -/

theorem q_pos {α : ℝ} (hα : 0 < α) (z : ℝ) : 0 < q α z := by
  rw [q, integral_pos_iff_support_of_nonneg (fun u => w_nonneg α z u) (integrable_w hα z)]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (w α z) := fun u hu => by
    have hu : 0 < u := hu
    simp only [Function.mem_support, w]
    exact (mul_pos (rpow_pos_of_pos (abs_pos.2 hu.ne') _) (exp_pos _)).ne'
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

/-- `∫ (u - z)² w = q'' + q`. -/
theorem integral_sq_w {α : ℝ} (hα : 0 < α) (z : ℝ) :
    ∫ u, (u - z) ^ 2 * w α z u = q2 α z + q α z := by
  rw [q2, q, ← integral_add (integrable_q2 hα z) (integrable_w hα z)]
  congr 1; funext u; ring

/-- **Cauchy–Schwarz for the posterior**: `q'² ≤ q (q'' + q)`. -/
theorem q1_sq_le {α : ℝ} (hα : 0 < α) (z : ℝ) : q1 α z ^ 2 ≤ q α z * (q2 α z + q α z) := by
  set t := q1 α z / q α z
  have hq := q_pos hα z
  have hnn : 0 ≤ ∫ u, ((u - z) - t) ^ 2 * w α z u :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (w_nonneg α z u)
  have hexp : ∫ u, ((u - z) - t) ^ 2 * w α z u =
      (q2 α z + q α z) - 2 * t * q1 α z + t ^ 2 * q α z := by
    have e : (fun u => ((u - z) - t) ^ 2 * w α z u) =
        fun u => ((u - z) ^ 2 * w α z u - (2 * t) * ((u - z) * w α z u)) + t ^ 2 * w α z u := by
      funext u; ring
    have i2 : Integrable (fun u => (u - z) ^ 2 * w α z u) :=
      ((integrable_q2 hα z).add (integrable_w hα z)).congr
        (Eventually.of_forall fun u => by simp only [Pi.add_apply]; ring)
    have j3 : Integrable (fun u => 2 * t * ((u - z) * w α z u)) := (integrable_q1 hα z).const_mul _
    have j1 : Integrable (fun u => (u - z) ^ 2 * w α z u - 2 * t * ((u - z) * w α z u)) := i2.sub j3
    have j2 : Integrable (fun u => t ^ 2 * w α z u) := (integrable_w hα z).const_mul _
    rw [e, integral_add j1 j2, integral_sub i2 j3, integral_const_mul, integral_const_mul,
      integral_sq_w hα z]
    rfl
  rw [hexp] at hnn
  have ht : t * q α z = q1 α z := div_mul_cancel₀ _ hq.ne'
  nlinarith [ht]

/-- The log-derivative `L' = q'/q`. -/
def L1 (α z : ℝ) : ℝ := q1 α z / q α z

/-- From Cauchy–Schwarz and the ODE: `L'² ≤ α - z L'`. -/
theorem L1_sq_le {α : ℝ} (hα : 0 < α) (z : ℝ) : L1 α z ^ 2 ≤ α - z * L1 α z := by
  have hq := q_pos hα z
  have hcs := q1_sq_le hα z
  have hode := ode hα z
  rw [L1, div_pow, div_le_iff₀ (by positivity)]
  have : (α - z * (q1 α z / q α z)) * q α z ^ 2 = q α z * (q2 α z + q α z) := by
    field_simp
    nlinarith [hode]
  linarith

/-- **Growth bound**: `|L'(z)| ≤ |z| + √α`. -/
theorem abs_L1_le {α : ℝ} (hα : 0 < α) (z : ℝ) : |L1 α z| ≤ |z| + √α := by
  have h := L1_sq_le hα z
  have hs : √α ^ 2 = α := sq_sqrt hα.le
  have hzl : -(z * L1 α z) ≤ |z| * |L1 α z| := by
    rw [← abs_mul]; exact neg_le_abs _
  by_contra hc
  rw [not_le] at hc
  have hsq : 0 ≤ √α := sqrt_nonneg α
  have hLpos : 0 < |L1 α z| := lt_of_le_of_lt (by positivity) hc
  have h1 : |L1 α z| * (|z| + √α) < |L1 α z| * |L1 α z| := mul_lt_mul_of_pos_left hc hLpos
  have hgt : √α < |L1 α z| := lt_of_le_of_lt (le_add_of_nonneg_left (abs_nonneg z)) hc
  have h2 : α ≤ |L1 α z| * √α := by nlinarith
  have h3 : |L1 α z| * |L1 α z| = L1 α z ^ 2 := by rw [← sq, sq_abs]
  nlinarith

/-! ### Gaussian integration by parts -/

/-- The standard Gaussian weight `e^{-z²/2}` (unnormalized). -/
def gauss (z : ℝ) : ℝ := exp (-(1 / 2) * z ^ 2)

theorem hasDerivAt_gauss (z : ℝ) : HasDerivAt gauss (-z * gauss z) z := by
  have h : HasDerivAt (fun z : ℝ => -(1 / 2) * z ^ 2) (-z) z :=
    ((hasDerivAt_pow 2 z).const_mul (-(1 / 2))).congr_deriv (by ring)
  exact h.exp.congr_deriv (by simp only [gauss]; ring)

theorem integrable_poly_gauss {f : ℝ → ℝ} (hf : AEStronglyMeasurable f) {A B : ℝ}
    (hb : ∀ z, |f z| ≤ A + B * z ^ 2) : Integrable (fun z => f z * gauss z) := by
  have h0 := integrable_abs_rpow_mul_exp (b := 1 / 2) (by norm_num) (s := 0) (by norm_num)
  have h2 := integrable_abs_rpow_mul_exp (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
  refine ((h0.const_mul |A|).add (h2.const_mul |B|)).mono'
    (hf.mul (by unfold gauss; fun_prop)) (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_mul, gauss, abs_of_pos (exp_pos _), Pi.add_apply, rpow_zero,
    rpow_two, sq_abs, one_mul]
  have hz := hb z
  have e : 0 < exp (-(1 / 2) * z ^ 2) := exp_pos _
  have : A + B * z ^ 2 ≤ |A| + |B| * z ^ 2 := by
    nlinarith [le_abs_self A, le_abs_self B, sq_nonneg z]
  nlinarith

/-- **Gaussian integration by parts** (Stein's identity) for `g` of linear growth with
derivative of quadratic growth: `∫ g' e^{-z²/2} = ∫ z g e^{-z²/2}`. -/
theorem gaussian_ibp {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z)
    (hg'm : AEStronglyMeasurable g') {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgb : ∀ z, |g z| ≤ A + B * |z|) (hg'b : ∀ z, |g' z| ≤ C + D * z ^ 2) :
    ∫ z, g' z * gauss z = ∫ z, z * g z * gauss z := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hg z).continuousAt
  have hgm : AEStronglyMeasurable g := hgc.aestronglyMeasurable
  have hz : ∀ z : ℝ, |z| ≤ 1 + z ^ 2 := fun z => by nlinarith [sq_abs z, abs_nonneg z]
  -- the three integrable pieces
  have i1 : Integrable (fun z => g' z * gauss z) := integrable_poly_gauss hg'm hg'b
  have i2 : Integrable (fun z => (z * g z) * gauss z) :=
    integrable_poly_gauss (continuous_id.mul hgc).aestronglyMeasurable (A := A) (B := A + B)
      fun z => by
        rw [abs_mul]
        have := hgb z
        have h1 : |z| * |g z| ≤ |z| * (A + B * |z|) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg z)
        nlinarith [hz z, sq_abs z, abs_nonneg z]
  have i3 : Integrable (fun z => g z * gauss z) :=
    integrable_poly_gauss hgm (A := A + B) (B := B) fun z => by
      have := hgb z; nlinarith [hz z]
  -- derivative of `g · gauss`, and its integrability
  have hd : ∀ z, HasDerivAt (fun z => g z * gauss z) (g' z * gauss z + g z * (-z * gauss z)) z :=
    fun z => (hg z).mul (hasDerivAt_gauss z)
  have i4 : Integrable (fun z => g' z * gauss z + g z * (-z * gauss z)) :=
    (i1.sub i2).congr (Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)
  have htop := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun z _ => hd z)
    i4.integrableOn i3.integrableOn
  have hbot := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun z _ => hd z)
    i4.integrableOn i3.integrableOn
  have key := integral_mul_deriv_eq_deriv_mul (u := g) (v := gauss) (u' := g')
    (v' := fun z => -z * gauss z) (fun z _ => hg z) (fun z _ => hasDerivAt_gauss z)
    (i2.neg.congr (Eventually.of_forall fun z => by simp only [Pi.neg_apply, Pi.mul_apply]; ring))
    i1 hbot htop
  have e1 : ∫ z, g z * (-z * gauss z) = -∫ z, z * g z * gauss z := by
    rw [← integral_neg]; congr 1; funext z; ring
  rw [e1] at key
  linarith

/-! ### The log-derivative's derivative, and the main identity -/

/-- `L'' = q''/q - (q'/q)²`. -/
def L2 (α z : ℝ) : ℝ := q2 α z / q α z - (q1 α z / q α z) ^ 2

theorem hasDerivAt_L1 {α : ℝ} (hα : 0 < α) (z : ℝ) : HasDerivAt (L1 α) (L2 α z) z := by
  have hq := (q_pos hα z).ne'
  exact ((hasDerivAt_q1 hα z).div (hasDerivAt_q hα z) hq).congr_deriv (by
    simp only [L2]; field_simp)

/-- The ODE in log form: `L'' = (α - 1) - z L' - L'²`. -/
theorem L2_eq {α : ℝ} (hα : 0 < α) (z : ℝ) : L2 α z = (α - 1) - z * L1 α z - L1 α z ^ 2 := by
  have hq := (q_pos hα z).ne'
  have hode := ode hα z
  have h2 : q2 α z = (α - 1) * q α z - z * q1 α z := by linarith
  simp only [L2, L1, h2]
  field_simp

theorem abs_L2_le {α : ℝ} (hα : 0 < α) (z : ℝ) :
    |L2 α z| ≤ (|α - 1| + 3 * α) + 4 * z ^ 2 := by
  rw [L2_eq hα z]
  have hL := abs_L1_le hα z
  have hs : √α ^ 2 = α := sq_sqrt hα.le
  have hsq := sqrt_nonneg α
  have hL0 := abs_nonneg (L1 α z)
  have hzL : |z * L1 α z| ≤ |z| * (|z| + √α) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg z)
  have hL2 : L1 α z ^ 2 ≤ (|z| + √α) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hL0 hL 2
  have hamgm : |z| * √α ≤ (z ^ 2 + α) / 2 := by nlinarith [sq_nonneg (|z| - √α), sq_abs z]
  calc |α - 1 - z * L1 α z - L1 α z ^ 2|
      ≤ |α - 1| + |z * L1 α z| + L1 α z ^ 2 := by
        have := abs_sub (α - 1 - z * L1 α z) (L1 α z ^ 2)
        have := abs_sub (α - 1) (z * L1 α z)
        rw [abs_of_nonneg (sq_nonneg (L1 α z))] at *
        linarith
    _ ≤ (|α - 1| + 3 * α) + 4 * z ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]

/-- **Main identity (unnormalized)**: `∫ (z + L'(z))² e^{-z²/2} = α ∫ e^{-z²/2}`. -/
theorem moment_identity {α : ℝ} (hα : 0 < α) :
    ∫ z, (z + L1 α z) ^ 2 * gauss z = α * ∫ z, gauss z := by
  have hL1c : Continuous (L1 α) := continuous_iff_continuousAt.2 fun z => (hasDerivAt_L1 hα z).continuousAt
  have hL1b : ∀ z, |L1 α z| ≤ √α + 1 * |z| := fun z => by linarith [abs_L1_le hα z]
  -- Stein for `g = L'` and for `g = id`
  have ibp1 := gaussian_ibp (g := L1 α) (g' := L2 α) (hasDerivAt_L1 hα)
    (by
      have : L2 α = fun z => (α - 1) - z * L1 α z - L1 α z ^ 2 := funext (L2_eq hα)
      rw [this]; exact (by fun_prop : Continuous fun z => (α - 1) - z * L1 α z - L1 α z ^ 2).aestronglyMeasurable)
    (sqrt_nonneg α) zero_le_one hL1b (abs_L2_le hα)
  have ibp2 := gaussian_ibp (g := id) (g' := fun _ => 1) (fun z => hasDerivAt_id z)
    aestronglyMeasurable_const le_rfl zero_le_one (fun z => by simp) (C := 1) (D := 0)
    (fun z => by simp)
  -- integrability of the pieces
  have hz2 : Integrable (fun z => z ^ 2 * gauss z) :=
    integrable_poly_gauss (by fun_prop) (A := 0) (B := 1) fun z => by simp
  have hzL : Integrable (fun z => z * L1 α z * gauss z) :=
    integrable_poly_gauss (continuous_id.mul hL1c).aestronglyMeasurable (A := α + 1) (B := 2)
      fun z => by
        rw [abs_mul]
        have := abs_L1_le hα z
        have h1 : |z| * |L1 α z| ≤ |z| * (|z| + √α) := mul_le_mul_of_nonneg_left this (abs_nonneg z)
        nlinarith [sq_abs z, abs_nonneg z, sq_sqrt hα.le, sqrt_nonneg α, sq_nonneg (|z| - √α)]
  have hg : Integrable gauss := by
    simpa using integrable_poly_gauss (f := fun _ => 1) aestronglyMeasurable_const (A := 1) (B := 0)
      (fun z => by simp)
  have hL2i : Integrable (fun z => L2 α z * gauss z) :=
    integrable_poly_gauss (by
      have : L2 α = fun z => (α - 1) - z * L1 α z - L1 α z ^ 2 := funext (L2_eq hα)
      rw [this]; exact (by fun_prop : Continuous fun z => (α - 1) - z * L1 α z - L1 α z ^ 2).aestronglyMeasurable)
      (abs_L2_le hα)
  -- pointwise: (z + L')² = z² + z L' + (α - 1) - L''
  have hpt : ∀ z, (z + L1 α z) ^ 2 * gauss z =
      z ^ 2 * gauss z + z * L1 α z * gauss z + (α - 1) * gauss z - L2 α z * gauss z := fun z => by
    rw [L2_eq hα z]; ring
  simp_rw [hpt]
  have j1 : Integrable (fun z => z ^ 2 * gauss z + z * L1 α z * gauss z) := hz2.add hzL
  have j2 : Integrable (fun z => (α - 1) * gauss z) := hg.const_mul _
  have j3 : Integrable (fun z => z ^ 2 * gauss z + z * L1 α z * gauss z + (α - 1) * gauss z) :=
    j1.add j2
  rw [integral_sub j3 hL2i, integral_add j1 j2, integral_add hz2 hzL, integral_const_mul]
  have e2 : ∫ z, z ^ 2 * gauss z = ∫ z, gauss z := by
    have h := ibp2
    simp only [one_mul, id] at h
    rw [h]; congr 1; funext z; ring
  rw [e2, ibp1]
  ring

/-! ### The statement for the posterior mean under `N(0, 1)` -/

/-- The posterior mean of `u` given `z`, for the prior `|u|^{α-1}` and likelihood `N(u, 1)`. -/
def postMean (α z : ℝ) : ℝ := (∫ u, u * w α z u) / q α z

theorem postMean_eq {α : ℝ} (hα : 0 < α) (z : ℝ) : postMean α z = z + L1 α z := by
  have hq := (q_pos hα z).ne'
  have h : ∫ u, u * w α z u = q1 α z + z * q α z := by
    rw [q1, q, ← integral_const_mul, ← integral_add (integrable_q1 hα z)
      ((integrable_w hα z).const_mul z)]
    congr 1; funext u; ring
  rw [postMean, h, L1]
  field_simp
  ring

/-- **Bayes second moment for the scale-invariant prior.** With `z ~ N(0, 1)` (the truth
`u = 0`), the posterior mean `m(z)` for the prior `|u|^{α-1}` satisfies `E[m(z)²] = α`.

For the toy models `y = a·bᵏ·x` this is the Bayes generalization coefficient
`lim n E[G_n] = E[m²]/2 = α/2 = 1/(2k)`, the learning coefficient. -/
theorem bayes_second_moment {α : ℝ} (hα : 0 < α) :
    ∫ z, postMean α z ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = α := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpdf : ∀ x, ProbabilityTheory.gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * gauss x := fun x => by
    simp only [ProbabilityTheory.gaussianPDFReal, gauss, NNReal.coe_one, mul_one, sub_zero]
    congr 2; ring
  simp_rw [smul_eq_mul, hpdf, postMean_eq hα]
  have e : (fun x => (√(2 * π))⁻¹ * gauss x * (x + L1 α x) ^ 2) =
      fun x => (√(2 * π))⁻¹ * ((x + L1 α x) ^ 2 * gauss x) := by funext x; ring
  rw [e, integral_const_mul, moment_identity hα]
  have hg : ∫ z, gauss z = √(2 * π) := by
    simp only [gauss]
    rw [integral_gaussian]; congr 1; ring
  rw [hg]
  have : 0 < √(2 * π) := by positivity
  field_simp

end OpenTheory.BayesToy
