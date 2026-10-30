import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The learning coefficient of a normal-crossing model

Singular learning theory (Watanabe) governs Bayesian learning by the *real log canonical
threshold* (RLCT) `λ` of the population loss `K ≥ 0` against the prior `φ`: the zeta integral
`∫ K^{-s} φ` is finite exactly for `s < λ` (`IsRLCT`), and its meromorphic continuation
`ζ(z) = ∫ K^z φ` has its largest pole at `-λ`.

Resolution of singularities (`formal/core/Theory/Training/Singular/Resolution.lean`) reduces every analytic `K` to
finitely many charts where `K` and the Jacobian are monomials up to units. This file computes
everything on the monomial model itself, the open cube `(0,1)^d` with

  `K(y) = ∏ yᵢ^{2kᵢ}`,  `φ(y) = ∏ yᵢ^{hᵢ}`:

* `isRLCT_monomial`: `λ = minᵢ (hᵢ + 1) / (2kᵢ)` over the coordinates with `kᵢ > 0`;
* `zeta_monomial`: `∫ K^z φ = ∏ᵢ 1 / (2kᵢ z + hᵢ + 1)`, with poles at `-(hᵢ + 1)/(2kᵢ)`;
* `partition_lower`, `freeEnergy_le`: the partition function `Z(n) = ∫ e^{-nK} φ` is at least
  `e⁻¹ n^{-λ} ∏ 1/(hᵢ+1)`, so the free energy `-log Z(n)` is at most `λ log n + O(1)`;
* `isRLCT_toy`: the toy model `y = a bᵏ x` has `K = a² b^{2k}` and `λ = 1/(2k)`, the Bayes
  coefficient of `OpenTheory.BayesToy.bayes_second_moment` at `α = 1/k`.

Tonelli on `(Fin d → ℝ)` for products of one-variable functions, `lintegral_fin_prod_eq_prod`,
is the `lintegral` form of Mathlib's `integral_fin_nat_prod_eq_prod`.
-/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal

namespace OpenTheory.Singular

/-! ### The zeta integral and the RLCT -/

/-- The zeta integral `∫ K^{-s} φ dμ` in `[0, ∞]`. At zeros of `K` the integrand is `∞` for
`s > 0` (`ENNReal.rpow` of `0` at a negative exponent). -/
def zetaIntegral {E : Type*} [MeasurableSpace E] (K φ : E → ℝ) (μ : Measure E) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (K w) ^ (-s) * ENNReal.ofReal (φ w) ∂μ

/-- `λ` is the *real log canonical threshold* of `K` against `φ`: for `s ≥ 0`, the zeta integral
`∫ K^{-s} φ` is finite exactly when `s < λ`. -/
def IsRLCT {E : Type*} [MeasurableSpace E] (K φ : E → ℝ) (μ : Measure E) (lam : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → (zetaIntegral K φ μ s < ⊤ ↔ s < lam)

/-- A positive RLCT is unique. -/
theorem IsRLCT.unique {E : Type*} [MeasurableSpace E] {K φ : E → ℝ} {μ : Measure E} {a b : ℝ}
    (ha : IsRLCT K φ μ a) (hb : IsRLCT K φ μ b) (ha0 : 0 < a) (hb0 : 0 < b) : a = b := by
  by_contra hne
  have hs : 0 ≤ (a + b) / 2 := by positivity
  rcases lt_or_gt_of_ne hne with h | h
  · linarith [(ha _ hs).1 ((hb _ hs).2 (by linarith))]
  · linarith [(hb _ hs).1 ((ha _ hs).2 (by linarith))]

/-! ### Tonelli for products of one-variable functions -/

/-- **Tonelli** in `n` variables for a product of one-variable functions. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {μ : Fin n → Measure ℝ} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : ℝ × (Fin n → ℝ), f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂((μ 0).prod (Measure.pi fun i => μ i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        rw [← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable]
        exact (Finset.measurable_prod _ fun i _ =>
          (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
      _ = _ := by rw [Fin.prod_univ_succ]

/-! ### One variable -/

theorem lintegral_Ioo_rpow_lt_top_iff (a : ℝ) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ a) < ⊤ ↔ -1 < a := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x : ℝ => x ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact rpow_nonneg hx.1.le a
  rw [← hasFiniteIntegral_iff_ofReal hnn, ← intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  exact ⟨fun h => ⟨(measurable_id.pow_const a).aestronglyMeasurable, h⟩, fun h => h.2⟩

theorem lintegral_Ioo_rpow_pos (a : ℝ) : 0 < ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ a) := by
  rw [lintegral_pos_iff_support (by fun_prop), Measure.restrict_apply' measurableSet_Ioo]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (fun x : ℝ => ENNReal.ofReal (x ^ a)) ∩ Ioo 0 1 :=
    fun x hx => ⟨by simp [Function.mem_support, rpow_pos_of_pos hx.1], hx⟩
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

theorem integral_Ioo_rpow {a : ℝ} (ha : -1 < a) : ∫ x in Ioo (0 : ℝ) 1, x ^ a = 1 / (a + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), one_rpow, zero_rpow (by linarith)]
  ring

theorem lintegral_Ioo_pow (t : ℝ) (ht : 0 ≤ t) (h : ℕ) :
    ∫⁻ x in Ioo (0 : ℝ) t, ENNReal.ofReal (x ^ h) = ENNReal.ofReal (t ^ (h + 1) / (h + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht, integral_pow]
    simp
  · exact (continuous_pow h).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact pow_nonneg hx.1.le h

/-! ### The monomial model on the cube -/

/-- The open unit cube `(0,1)^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := univ.pi fun _ => Ioo 0 1

theorem measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem restrict_cube (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (cube d) =
      Measure.pi fun _ => volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [cube, volume_pi, Measure.restrict_pi_pi]

/-- The loss in normal-crossing form, `K(y) = ∏ yᵢ^{2kᵢ}`. -/
def monomialLoss {d : ℕ} (k : Fin d → ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, y i ^ (2 * k i)

/-- The prior density in normal-crossing form, `φ(y) = ∏ yᵢ^{hᵢ}`. -/
def monomialPrior {d : ℕ} (h : Fin d → ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, y i ^ h i

/-- On the cube, `K^z φ = ∏ yᵢ^{hᵢ + 2kᵢz}`. -/
theorem monomialLoss_rpow_mul {d : ℕ} (k h : Fin d → ℕ) (z : ℝ) {y : Fin d → ℝ}
    (hy : y ∈ cube d) :
    monomialLoss k y ^ z * monomialPrior h y = ∏ i, y i ^ ((h i : ℝ) + 2 * k i * z) := by
  have hy0 : ∀ i, 0 < y i := fun i => (hy i (mem_univ i)).1
  rw [monomialLoss, monomialPrior, ← Real.finsetProd_rpow _ _
    (fun i _ => pow_nonneg (hy0 i).le _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (hy0 i).le, ← rpow_add (hy0 i), add_comm]
  push_cast
  ring_nf

/-- On the cube, the zeta integrand is a product of one-variable powers. -/
theorem zetaIntegrand_eq_prod {d : ℕ} (k h : Fin d → ℕ) (s : ℝ) {y : Fin d → ℝ}
    (hy : y ∈ cube d) :
    ENNReal.ofReal (monomialLoss k y) ^ (-s) * ENNReal.ofReal (monomialPrior h y) =
      ∏ i, ENNReal.ofReal (y i ^ ((h i : ℝ) - 2 * k i * s)) := by
  have hy0 : ∀ i, 0 < y i := fun i => (hy i (mem_univ i)).1
  have hK : 0 < monomialLoss k y := Finset.prod_pos fun i _ => pow_pos (hy0 i) _
  have hφ : 0 ≤ monomialPrior h y := Finset.prod_nonneg fun i _ => pow_nonneg (hy0 i).le _
  rw [ENNReal.ofReal_rpow_of_pos hK, ← ENNReal.ofReal_mul (rpow_nonneg hK.le _),
    monomialLoss_rpow_mul k h (-s) hy,
    ENNReal.ofReal_prod_of_nonneg fun i _ => rpow_nonneg (hy0 i).le _]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring_nf

/-- The zeta integral of the monomial model factorizes over the coordinates. -/
theorem zetaIntegral_monomial {d : ℕ} (k h : Fin d → ℕ) (s : ℝ) :
    zetaIntegral (monomialLoss k) (monomialPrior h) (volume.restrict (cube d)) s =
      ∏ i, ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ ((h i : ℝ) - 2 * k i * s)) := by
  rw [zetaIntegral, setLIntegral_congr_fun (measurableSet_cube d)
    (fun y hy => zetaIntegrand_eq_prod k h s hy), restrict_cube]
  exact lintegral_fin_prod_eq_prod (fun i x => ENNReal.ofReal (x ^ ((h i : ℝ) - 2 * k i * s)))
    fun i => (measurable_id.pow_const _).ennreal_ofReal

/-- **The RLCT of a normal-crossing model** is `λ = minᵢ (hᵢ + 1)/(2kᵢ)` over the coordinates
with `kᵢ > 0`. -/
theorem isRLCT_monomial {d : ℕ} (k h : Fin d → ℕ) {lam : ℝ}
    (hatt : ∃ i, 0 < k i ∧ lam = (h i + 1) / (2 * k i))
    (hmin : ∀ i, 0 < k i → lam ≤ (h i + 1) / (2 * k i)) :
    IsRLCT (monomialLoss k) (monomialPrior h) (volume.restrict (cube d)) lam := by
  intro s _
  rw [zetaIntegral_monomial]
  set F : Fin d → ℝ≥0∞ := fun i =>
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ ((h i : ℝ) - 2 * k i * s))
  have hprod : ∏ i, F i < ⊤ ↔ ∀ i, F i < ⊤ := by
    refine ⟨fun hlt i => lt_top_iff_ne_top.2 fun hi => ?_, fun h => ENNReal.prod_lt_top
      fun i _ => h i⟩
    exact hlt.ne (WithTop.prod_eq_top (Finset.mem_univ i) hi
      fun j _ => (lintegral_Ioo_rpow_pos _).ne')
  rw [hprod]
  simp only [F, lintegral_Ioo_rpow_lt_top_iff]
  constructor
  · intro hall
    obtain ⟨i, hk, rfl⟩ := hatt
    have hk' : (0 : ℝ) < 2 * k i := by positivity
    rw [lt_div_iff₀ hk']
    linarith [hall i]
  · intro hs i
    rcases Nat.eq_zero_or_pos (k i) with hk | hk
    · simp only [hk, CharP.cast_eq_zero, mul_zero, zero_mul, sub_zero]
      linarith [(Nat.cast_nonneg (h i) : (0 : ℝ) ≤ h i)]
    · have hk' : (0 : ℝ) < 2 * k i := by positivity
      have := (lt_div_iff₀ hk').1 (hs.trans_le (hmin i hk))
      linarith

/-- **The zeta function of a normal-crossing model**: for real `z` right of every pole,
`∫ K^z φ = ∏ᵢ 1/(2kᵢz + hᵢ + 1)`. The poles `-(hᵢ+1)/(2kᵢ)` have largest element `-λ`. -/
theorem zeta_monomial {d : ℕ} (k h : Fin d → ℕ) {z : ℝ}
    (hz : ∀ i, -1 < (h i : ℝ) + 2 * k i * z) :
    ∫ y in cube d, monomialLoss k y ^ z * monomialPrior h y =
      ∏ i, 1 / (2 * k i * z + h i + 1) := by
  rw [setIntegral_congr_fun (measurableSet_cube d) fun y hy => monomialLoss_rpow_mul k h z hy,
    restrict_cube, integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun i x => x ^ ((h i : ℝ) + 2 * k i * z))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_Ioo_rpow (hz i)]
  ring_nf

/-! ### The partition function and the free energy -/

theorem measurable_monomialLoss {d : ℕ} (k : Fin d → ℕ) : Measurable (monomialLoss k) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

theorem measurable_monomialPrior {d : ℕ} (h : Fin d → ℕ) : Measurable (monomialPrior h) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

/-- **Laplace lower bound.** If coordinate `i₀` has `k_{i₀} > 0`, then for `n ≥ 1` the partition
function `Z(n) = ∫ e^{-nK} φ` over the cube is at least `e⁻¹ n^{-(h_{i₀}+1)/(2k_{i₀})} ∏ 1/(hᵢ+1)`:
on the box where `y_{i₀} < n^{-1/(2k_{i₀})}`, `nK ≤ 1`. -/
theorem partition_lower {d : ℕ} (k h : Fin d → ℕ) {i₀ : Fin d} (hk : 0 < k i₀) {n : ℝ}
    (hn : 1 ≤ n) :
    ENNReal.ofReal (exp (-1) * (∏ i, 1 / ((h i : ℝ) + 1)) *
        n ^ (-(((h i₀ : ℝ) + 1) / (2 * k i₀)))) ≤
      ∫⁻ y in cube d, ENNReal.ofReal (exp (-(n * monomialLoss k y)) * monomialPrior h y) := by
  have hn0 : 0 < n := by linarith
  have hk0 : (k i₀ : ℝ) ≠ 0 := by positivity
  set t : ℝ := n ^ (-(1 / (2 * (k i₀ : ℝ)))) with ht_def
  have ht0 : 0 < t := rpow_pos_of_pos hn0 _
  have ht1 : t ≤ 1 := rpow_le_one_of_one_le_of_nonpos hn (by simp only [neg_nonpos]; positivity)
  have htk : t ^ (2 * k i₀) = n⁻¹ := by
    rw [ht_def, ← rpow_natCast, ← rpow_mul hn0.le,
      show -(1 / (2 * (k i₀ : ℝ))) * ((2 * k i₀ : ℕ) : ℝ) = -1 by push_cast; field_simp,
      rpow_neg_one]
  set b : Fin d → ℝ := Function.update (fun _ => (1 : ℝ)) i₀ t with hb_def
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    simp only [b, Function.update_apply]; split_ifs <;> positivity
  have hb1 : ∀ i, b i ≤ 1 := fun i => by
    simp only [b, Function.update_apply]; split_ifs <;> linarith
  -- the box `∏ (0, bᵢ)` inside the cube
  obtain ⟨B, hB⟩ : ∃ B : Set (Fin d → ℝ), B = univ.pi fun i => Ioo 0 (b i) := ⟨_, rfl⟩
  have hBmem : ∀ y ∈ B, ∀ i, y i ∈ Ioo 0 (b i) := fun y hy i => by
    rw [hB] at hy; exact hy i (mem_univ i)
  have hBsub : B ⊆ cube d := fun y hy i _ =>
    ⟨(hBmem y hy i).1, (hBmem y hy i).2.trans_le (hb1 i)⟩
  -- on the box, `n K ≤ 1`
  have hbound : ∀ y ∈ B, ENNReal.ofReal (exp (-1)) * ENNReal.ofReal (monomialPrior h y) ≤
      ENNReal.ofReal (exp (-(n * monomialLoss k y)) * monomialPrior h y) := by
    intro y hy
    have hy0 : ∀ i, 0 < y i := fun i => (hBmem y hy i).1
    have hy1 : ∀ i, y i < 1 := fun i => (hBmem y hy i).2.trans_le (hb1 i)
    rw [← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun i _ => pow_nonneg (hy0 i).le _))
    refine exp_le_exp.2 (neg_le_neg ?_)
    have hle : monomialLoss k y ≤ y i₀ ^ (2 * k i₀) := by
      rw [monomialLoss, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
      refine mul_le_of_le_one_right (pow_nonneg (hy0 i₀).le _) ?_
      exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (hy0 i).le _)
        fun i _ => pow_le_one₀ (hy0 i).le (hy1 i).le
    have hyt : y i₀ < t := by simpa [b] using (hBmem y hy i₀).2
    have : y i₀ ^ (2 * k i₀) ≤ n⁻¹ := htk ▸ pow_le_pow_left₀ (hy0 i₀).le hyt.le _
    calc n * monomialLoss k y ≤ n * n⁻¹ := mul_le_mul_of_nonneg_left (hle.trans this) hn0.le
      _ = 1 := mul_inv_cancel₀ hn0.ne'
  -- the integral of the prior over the box
  have hbox : ∫⁻ y in B, ENNReal.ofReal (monomialPrior h y) =
      ∏ i, ENNReal.ofReal (b i ^ (h i + 1) / (h i + 1)) := by
    have hcongr : EqOn (fun y => ENNReal.ofReal (monomialPrior h y))
        (fun y => ∏ i, ENNReal.ofReal (y i ^ h i)) B := fun y hy =>
      ENNReal.ofReal_prod_of_nonneg fun i _ => pow_nonneg (hBmem y hy i).1.le _
    rw [setLIntegral_congr_fun (hB ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioo) hcongr,
      hB, volume_pi, Measure.restrict_pi_pi,
      lintegral_fin_prod_eq_prod (fun i x => ENNReal.ofReal (x ^ h i))
        fun i => (measurable_id.pow_const _).ennreal_ofReal]
    exact Finset.prod_congr rfl fun i _ => lintegral_Ioo_pow (b i) (hb0 i) (h i)
  have hprod : ∏ i, b i ^ (h i + 1) / ((h i : ℝ) + 1) =
      (∏ i, 1 / ((h i : ℝ) + 1)) * n ^ (-(((h i₀ : ℝ) + 1) / (2 * k i₀))) := by
    have : ∀ i, b i ^ (h i + 1) / ((h i : ℝ) + 1) =
        1 / ((h i : ℝ) + 1) * (if i₀ = i then t ^ (h i₀ + 1) else 1) := by
      intro i
      by_cases hi : i₀ = i
      · subst hi; simp [b]; ring
      · simp [b, hi, Ne.symm hi]
    rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib, Finset.prod_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [ht_def, ← rpow_natCast, ← rpow_mul hn0.le]
    push_cast
    congr 1
    field_simp
  calc ENNReal.ofReal (exp (-1) * (∏ i, 1 / ((h i : ℝ) + 1)) *
          n ^ (-(((h i₀ : ℝ) + 1) / (2 * k i₀))))
        = ENNReal.ofReal (exp (-1)) * ∫⁻ y in B, ENNReal.ofReal (monomialPrior h y) := by
          rw [hbox, ← ENNReal.ofReal_prod_of_nonneg
              fun i _ => div_nonneg (pow_nonneg (hb0 i) _) (by positivity),
            hprod, ← ENNReal.ofReal_mul (exp_pos _).le, mul_assoc]
      _ = ∫⁻ y in B, ENNReal.ofReal (exp (-1)) * ENNReal.ofReal (monomialPrior h y) :=
          (lintegral_const_mul _ (measurable_monomialPrior h).ennreal_ofReal).symm
      _ ≤ ∫⁻ y in B, ENNReal.ofReal (exp (-(n * monomialLoss k y)) * monomialPrior h y) :=
          setLIntegral_mono (((measurable_const.mul (measurable_monomialLoss k)).neg.exp.mul
            (measurable_monomialPrior h)).ennreal_ofReal) hbound
      _ ≤ _ := lintegral_mono_set hBsub

/-- The partition function `Z(n) = ∫_{(0,1)^d} e^{-nK} φ` of the monomial model. -/
def partition {d : ℕ} (k h : Fin d → ℕ) (n : ℝ) : ℝ :=
  ∫ y in cube d, exp (-(n * monomialLoss k y)) * monomialPrior h y

/-- **Free energy upper bound for a normal-crossing model.** With `λ = (h_{i₀}+1)/(2k_{i₀})` for
any coordinate with `k_{i₀} > 0` (in particular the minimizing one), for `n ≥ 1`
`-log Z(n) ≤ λ log n + 1 + ∑ᵢ log (hᵢ + 1)`. -/
theorem freeEnergy_le {d : ℕ} (k h : Fin d → ℕ) {i₀ : Fin d} (hk : 0 < k i₀) {n : ℝ}
    (hn : 1 ≤ n) :
    -log (partition k h n) ≤
      ((h i₀ : ℝ) + 1) / (2 * k i₀) * log n + 1 + ∑ i, log ((h i : ℝ) + 1) := by
  have hn0 : 0 < n := by linarith
  set c : ℝ := exp (-1) * (∏ i, 1 / ((h i : ℝ) + 1)) * n ^ (-(((h i₀ : ℝ) + 1) / (2 * k i₀)))
  have hc : 0 < c := by
    have : 0 < ∏ i, 1 / ((h i : ℝ) + 1) := Finset.prod_pos fun i _ => by positivity
    positivity
  have hmeas : Measurable fun y => exp (-(n * monomialLoss k y)) * monomialPrior h y :=
    (measurable_const.mul (measurable_monomialLoss k)).neg.exp.mul (measurable_monomialPrior h)
  have hcube : ∀ y ∈ cube d, ∀ i, y i ∈ Ioo (0 : ℝ) 1 := fun y hy i => hy i (mem_univ i)
  have hnn : ∀ y ∈ cube d, 0 ≤ exp (-(n * monomialLoss k y)) * monomialPrior h y :=
    fun y hy => mul_nonneg (exp_pos _).le
      (Finset.prod_nonneg fun i _ => pow_nonneg (hcube y hy i).1.le _)
  -- the lintegral is finite: the integrand is at most `1` on the cube
  have hfin : ∫⁻ y in cube d, ENNReal.ofReal (exp (-(n * monomialLoss k y)) * monomialPrior h y)
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in cube d, 1) ?_
      (setLIntegral_mono measurable_const fun y hy => ?_)
    · rw [setLIntegral_const, one_mul, cube, Real.volume_pi_Ioo]; simp
    · have hy0 : ∀ i, 0 < y i := fun i => (hcube y hy i).1
      have hy1 : ∀ i, y i < 1 := fun i => (hcube y hy i).2
      have he : exp (-(n * monomialLoss k y)) ≤ 1 :=
        exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hn0.le
          (Finset.prod_nonneg fun i _ => pow_nonneg (hy0 i).le _)))
      have hφ0 : 0 ≤ monomialPrior h y := Finset.prod_nonneg fun i _ => pow_nonneg (hy0 i).le _
      have hφ1 : monomialPrior h y ≤ 1 := Finset.prod_le_one₀
        (fun i _ => pow_nonneg (hy0 i).le _) fun i _ => pow_le_one₀ (hy0 i).le (hy1 i).le
      exact ENNReal.ofReal_le_one.2 (by nlinarith [exp_pos (-(n * monomialLoss k y))])
  have hZ : c ≤ partition k h n := by
    rw [partition, integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [ae_restrict_mem (measurableSet_cube d)] with y hy using hnn y hy)
      hmeas.aestronglyMeasurable]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (partition_lower k h hk hn)
  have hlog : log c ≤ log (partition k h n) := log_le_log hc hZ
  have hcl : log c = -1 - ∑ i, log ((h i : ℝ) + 1) -
      ((h i₀ : ℝ) + 1) / (2 * k i₀) * log n := by
    have hpos : ∀ i ∈ Finset.univ, (1 / ((h i : ℝ) + 1)) ≠ 0 := fun i _ => by positivity
    rw [log_mul (by positivity) (by positivity), log_mul (by positivity)
        (Finset.prod_pos fun i _ => by positivity).ne', log_exp, log_prod hpos,
      log_rpow hn0]
    simp only [one_div, log_inv, Finset.sum_neg_distrib]
    ring
  linarith

/-! ### The toy model `y = a bᵏ x` -/

/-- **RLCT of the toy model.** `K(a, b) = a² b^{2k}` with a uniform prior on `(0,1)²` has
`λ = 1/(2k)` for `k ≥ 1`: the Bayes coefficient `α/2` of `bayes_second_moment` at `α = 1/k`. -/
theorem isRLCT_toy {k : ℕ} (hk : 1 ≤ k) :
    IsRLCT (monomialLoss ![1, k]) (monomialPrior ![0, 0]) (volume.restrict (cube 2))
      (1 / (2 * k)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine isRLCT_monomial _ _ ⟨1, by simp; omega, by simp⟩ ?_
  intro i _
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, CharP.cast_eq_zero, zero_add,
      Nat.cast_one, mul_one]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · simp

end OpenTheory.Singular
