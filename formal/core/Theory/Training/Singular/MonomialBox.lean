import Theory.Training.Singular.NormalCrossing
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Monomials on coordinate boxes of `ℝⁿ`

After resolution of singularities, the zeta integral `∫ K^{-s} φ` is, on each chart, comparable to
`∫_B ∏ |yᵢ|^{aᵢ} dy` over a small box `B` around a point `c` with `aᵢ = βᵢ - s αᵢ`. This file
computes when that integral is finite. With the box chosen so that every coordinate of `c` is
either `0` or larger than the half-width in absolute value:

* `lintegral_box_prod`: Tonelli on a box of `EuclideanSpace ℝ (Fin n)`;
* `lintegral_box_monomial_lt_top_iff`: `∫_B ∏ |yᵢ|^{aᵢ} < ∞` iff `aᵢ > -1` at every coordinate
  with `cᵢ = 0`;
* `ae_coord_ne_zero`: almost every point has no zero coordinate.
-/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal

namespace OpenTheory.Singular

/-! ### One variable -/

theorem intervalIntegrable_abs_rpow {a r : ℝ} (ha : -1 < a) (hr : 0 ≤ r) :
    IntervalIntegrable (fun t : ℝ => |t| ^ a) volume (-r) r := by
  have h0 : IntervalIntegrable (fun t : ℝ => |t| ^ a) volume 0 r := by
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) ha).congr fun t ht => ?_
    rw [uIoc_of_le hr] at ht
    simp only [abs_of_pos ht.1]
  have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ a) volume (-r) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using h0.symm
  exact h1.trans h0

theorem lintegral_Ioo_rpow_lt_top_iff' {a r : ℝ} (hr : 0 < r) :
    ∫⁻ x in Ioo (0 : ℝ) r, ENNReal.ofReal (x ^ a) < ⊤ ↔ -1 < a := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] fun x : ℝ => x ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact rpow_nonneg hx.1.le a
  rw [← hasFiniteIntegral_iff_ofReal hnn, ← intervalIntegral.integrableOn_Ioo_rpow_iff hr]
  exact ⟨fun h => ⟨(measurable_id.pow_const a).aestronglyMeasurable, h⟩, fun h => h.2⟩

/-- Around `0`, `∫_{-r}^{r} |t|^a dt < ∞` iff `a > -1`. -/
theorem lintegral_Ioo_abs_rpow_lt_top_iff {c r a : ℝ} (hc : c = 0) (hr : 0 < r) :
    ∫⁻ t in Ioo (c - r) (c + r), ENNReal.ofReal (|t| ^ a) < ⊤ ↔ -1 < a := by
  subst hc
  rw [zero_sub, zero_add]
  constructor
  · intro h
    refine (lintegral_Ioo_rpow_lt_top_iff' hr).1 (lt_of_le_of_lt ?_ h)
    calc ∫⁻ x in Ioo (0 : ℝ) r, ENNReal.ofReal (x ^ a)
        = ∫⁻ x in Ioo (0 : ℝ) r, ENNReal.ofReal (|x| ^ a) :=
          setLIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [abs_of_pos hx.1]
      _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo_left (by linarith))
  · intro ha
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1
      (intervalIntegrable_abs_rpow ha hr.le)).lintegral_lt_top

/-- Away from `0`, `∫_{c-r}^{c+r} |t|^a dt` is finite for every `a`. -/
theorem lintegral_Ioo_abs_rpow_lt_top_of_lt {c r a : ℝ} (hr : r < |c|) :
    ∫⁻ t in Ioo (c - r) (c + r), ENNReal.ofReal (|t| ^ a) < ⊤ := by
  have hcont : ContinuousOn (fun t : ℝ => |t| ^ a) (Icc (c - r) (c + r)) := by
    refine continuous_abs.continuousOn.rpow_const fun t ht => Or.inl ?_
    have : |c| - |t - c| ≤ |t| := by
      have := abs_sub_abs_le_abs_sub c t
      rw [abs_sub_comm] at this
      linarith
    have : |t - c| ≤ r := abs_sub_le_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact (by linarith : (0 : ℝ) < |t|).ne'
  exact ((hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self).lintegral_lt_top

theorem lintegral_Ioo_abs_rpow_pos {c r a : ℝ} (hr : 0 < r) :
    0 < ∫⁻ t in Ioo (c - r) (c + r), ENNReal.ofReal (|t| ^ a) := by
  rw [lintegral_pos_iff_support (by fun_prop), Measure.restrict_apply' measurableSet_Ioo]
  have hsub : Ioo (c - r) (c + r) \ {0} ⊆
      Function.support (fun t : ℝ => ENNReal.ofReal (|t| ^ a)) ∩ Ioo (c - r) (c + r) :=
    fun t ht => by
      have ht0 : t ≠ 0 := ht.2
      have hpos : 0 < |t| ^ a := rpow_pos_of_pos (abs_pos.2 ht0) a
      exact ⟨by simpa [Function.mem_support] using hpos, ht.1⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_sdiff_null (measure_singleton 0), Real.volume_Ioo]
  simp only [ENNReal.ofReal_pos]
  linarith

/-! ### Boxes in `ℝⁿ` -/

variable {n : ℕ}

/-- The open coordinate box of half-width `r` around `c`. -/
def box (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ i, y i ∈ Ioo (c i - r) (c i + r)}

theorem box_eq_preimage (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    box c r = WithLp.ofLp ⁻¹' (univ.pi fun i => Ioo (c i - r) (c i + r)) := by
  ext y; simp [box]

theorem isOpen_box (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) : IsOpen (box c r) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)

theorem mem_box_self (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) : c ∈ box c r :=
  fun i => ⟨by linarith, by linarith⟩

/-- A box of half-width `r < ε / (n + 1)` lies in the Euclidean ball of radius `ε`. -/
theorem box_subset_ball (c : EuclideanSpace ℝ (Fin n)) {r ε : ℝ} (hr : 0 < r)
    (hrε : r < ε / (n + 1)) : box c r ⊆ Metric.ball c ε := by
  intro y hy
  have hε : 0 < ε := by
    have : 0 < ε / (n + 1) := hr.trans hrε
    exact (div_pos_iff_of_pos_right (by positivity)).1 this
  rw [Metric.mem_ball, EuclideanSpace.dist_eq, Real.sqrt_lt' hε]
  have hi : ∀ i, dist (y i) (c i) ^ 2 ≤ r ^ 2 := fun i => by
    have h := hy i
    have hlt : |y i - c i| < r := abs_sub_lt_iff.2 ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) hlt.le 2
  calc ∑ i, dist (y i) (c i) ^ 2 ≤ ∑ _i : Fin n, r ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = n * r ^ 2 := by simp
    _ ≤ ((n : ℝ) + 1) ^ 2 * r ^ 2 := by
        gcongr; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ < ε ^ 2 := by
        rw [lt_div_iff₀ (by positivity)] at hrε
        nlinarith [mul_pos hr (show (0 : ℝ) < n + 1 by positivity)]

/-- **Tonelli on a box.** -/
theorem lintegral_box_prod (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ y in box c r, ∏ i, f i (y i) = ∏ i, ∫⁻ t in Ioo (c i - r) (c i + r), f i t := by
  rw [box_eq_preimage, (PiLp.volume_preserving_ofLp (ι := Fin n)).setLIntegral_comp_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    (f := fun x : Fin n → ℝ => ∏ i, f i (x i))
    (Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)),
    volume_pi, Measure.restrict_pi_pi]
  exact lintegral_fin_prod_eq_prod _ hf

/-- Almost every point of `ℝⁿ` has no zero coordinate. -/
theorem ae_coord_ne_zero : ∀ᵐ y : EuclideanSpace ℝ (Fin n), ∀ i, y i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ x : Fin n → ℝ, x i ≠ 0 := by
    simpa [volume_pi] using Measure.ae_eval_ne (μ := fun _ : Fin n => (volume : Measure ℝ)) i 0
  exact (PiLp.volume_preserving_ofLp (ι := Fin n)).quasiMeasurePreserving.ae h

theorem volume_coord_eq_zero : volume {y : EuclideanSpace ℝ (Fin n) | ∃ i, y i = 0} = 0 := by
  have := ae_coord_ne_zero (n := n)
  rw [ae_iff] at this
  simpa using this

/-- **Monomials on a box.** If every coordinate of the centre is `0` or exceeds the half-width,
`∫_B ∏ |yᵢ|^{aᵢ} < ∞` iff `aᵢ > -1` at every coordinate where the centre vanishes. -/
theorem lintegral_box_monomial_lt_top_iff {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hc : ∀ i, c i = 0 ∨ r < |c i|) (a : Fin n → ℝ) :
    ∫⁻ y in box c r, ∏ i, ENNReal.ofReal (|y i| ^ a i) < ⊤ ↔ ∀ i, c i = 0 → -1 < a i := by
  rw [lintegral_box_prod c r (fun i t => ENNReal.ofReal (|t| ^ a i)) fun i => by fun_prop]
  set F : Fin n → ℝ≥0∞ := fun i => ∫⁻ t in Ioo (c i - r) (c i + r), ENNReal.ofReal (|t| ^ a i)
  have hprod : ∏ i, F i < ⊤ ↔ ∀ i, F i < ⊤ := by
    refine ⟨fun hlt i => lt_top_iff_ne_top.2 fun hi => ?_, fun h => ENNReal.prod_lt_top
      fun i _ => h i⟩
    exact hlt.ne (WithTop.prod_eq_top (Finset.mem_univ i) hi
      fun j _ => (lintegral_Ioo_abs_rpow_pos hr).ne')
  rw [hprod]
  refine forall_congr' fun i => ?_
  rcases hc i with h0 | hlt
  · simp only [F]
    rw [lintegral_Ioo_abs_rpow_lt_top_iff h0 hr]
    simp [h0]
  · have hne : c i ≠ 0 := fun h => by rw [h, abs_zero] at hlt; linarith
    simp only [F, lintegral_Ioo_abs_rpow_lt_top_of_lt hlt, hne, IsEmpty.forall_iff]

/-! ### Finite unions -/

theorem lintegral_finset_biUnion_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (t : Finset ι) (s : ι → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ ≤ ∑ i ∈ t, ∫⁻ a in s i, f a ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

end OpenTheory.Singular
