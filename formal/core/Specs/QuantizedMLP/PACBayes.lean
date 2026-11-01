import Specs.QuantizedMLP.Occam
import Theory.Learning.PACBayesCodes
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# PAC-Bayes certificates for quantized ReLU MLPs with a learned prior

The prior is a product over coordinates centred on a reference code `c`: each
coordinate keeps `c`'s level with mass `1 - 3·2^{-m}` and gives `2^{-m}` to each
other level. If `c` is trained on data independent of the bound sample, the
prior is fixed with respect to that sample and `catoni_grid` applies. Moving one
coordinate away from `c` costs about `m log 2` nats.

The probability is over the bound sample, conditional on the prior data. The
Dirac posterior at `c` itself costs `p · (-log (1 - 3·2^{-m}))` nats.
-/

noncomputable section
open MeasureTheory StatLean.StatisticalLearning OpenTheory.PACBayes

namespace OpenTheory.QuantizedMLP

/-- Per-coordinate weights of the prior centred on `c`. -/
def centredWeight (m : ℕ) {p : ℕ} (c : Code p 4) (i : Fin p) (v : Fin 4) : ℝ :=
  if v = c i then 1 - 3 / 2 ^ m else 1 / 2 ^ m

/-- The product prior centred on a reference code. -/
def centredPrior (m : ℕ) {p : ℕ} (c : Code p 4) : Code p 4 → ℝ :=
  prodDist (centredWeight m c)

theorem centre_mass_pos {m : ℕ} (hm : 2 ≤ m) : 0 < 1 - (3 : ℝ) / 2 ^ m := by
  have h4 : (4 : ℝ) ≤ 2 ^ m := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  rw [sub_pos, div_lt_one (by positivity)]; linarith

theorem centredWeight_pos {m : ℕ} (hm : 2 ≤ m) {p : ℕ} (c : Code p 4) (i : Fin p) (v : Fin 4) :
    0 < centredWeight m c i v := by
  unfold centredWeight
  split
  · exact centre_mass_pos hm
  · positivity

theorem centredWeight_sum (m : ℕ) {p : ℕ} (c : Code p 4) (i : Fin p) :
    ∑ v, centredWeight m c i v = 1 := by
  unfold centredWeight
  generalize c i = w
  fin_cases w <;> simp [Fin.sum_univ_four] <;> ring

theorem centredPrior_pos {m : ℕ} (hm : 2 ≤ m) {p : ℕ} (c : Code p 4) (h : Code p 4) :
    0 < centredPrior m c h :=
  prodDist_pos (centredWeight_pos hm c) h

theorem centredPrior_sum (m : ℕ) {p : ℕ} (c : Code p 4) : ∑ h, centredPrior m c h = 1 := by
  rw [centredPrior, sum_prodDist]
  simp [centredWeight_sum]

/-- The Dirac posterior at the centre costs at most `p · x / (1 - x)`, `x = 3·2^{-m}`. -/
theorem kl_dirac_centre_le {m : ℕ} (hm : 2 ≤ m) {p : ℕ} (c : Code p 4) :
    kl (dirac c) (centredPrior m c) ≤ p * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) := by
  rw [kl_dirac]
  have hx := centre_mass_pos hm
  have hcen : centredPrior m c c = (1 - 3 / 2 ^ m) ^ p := by
    simp [centredPrior, prodDist, centredWeight]
  rw [hcen, one_div, ← inv_pow, Real.log_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  calc Real.log (1 - 3 / 2 ^ m)⁻¹ ≤ (1 - 3 / 2 ^ m)⁻¹ - 1 := this
    _ = 3 / 2 ^ m / (1 - 3 / 2 ^ m) := by
        rw [eq_div_iff hx.ne', sub_mul, inv_mul_cancel₀ hx.ne']; ring

/-- **PAC-Bayes for quantized MLPs with a learned prior.** With probability
at least `1 - δ` over `n` IID observations independent of the reference code
`c`, every posterior on codes satisfies Catoni's inequality for every `t ∈ T`. -/
theorem mlp_pacBayes (P : Population Observation) (a : Arch) (c : Code a.parameterCount 4)
    {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (T : Finset ℝ) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    sampleLaw P.law n (⋃ t ∈ T,
      badEvent (classificationLoss a) P.law (centredPrior m c) n t (δ / T.card)) ≤
      ENNReal.ofReal δ :=
  catoni_grid (classificationLoss_range a) (classificationLoss_measurable a)
    (centredPrior_pos hm c) (centredPrior_sum m c) n T hT hδ

/-! ### Numerical inversion -/

/-- Rational inversion of Catoni's link from upper bounds on `exp c` and lower
bounds on `exp t`. -/
theorem risk_le_of_catoni {t c R E L : ℝ} (ht : 0 < t) (hc : 0 ≤ c)
    (hR : R ∈ Set.Icc (0 : ℝ) 1) (h : catoni t R ≤ c) (hE : Real.exp c ≤ E)
    (hL : L ≤ Real.exp t) (hL1 : 1 < L) :
    R ≤ (1 - 1 / E) / (1 - 1 / L) := by
  have hR' := (catoni_le_iff ht hR).1 h
  have hE0 : 0 < E := (Real.exp_pos c).trans_le hE
  have hnum : 1 - Real.exp (-c) ≤ 1 - 1 / E := by
    rw [Real.exp_neg, ← one_div]
    have := one_div_le_one_div_of_le (Real.exp_pos c) hE
    linarith
  have hden : 1 - 1 / L ≤ 1 - Real.exp (-t) := by
    rw [Real.exp_neg, ← one_div]
    have := one_div_le_one_div_of_le (by linarith) hL
    linarith
  have hden0 : 0 < 1 - 1 / L := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hL1
  have hnum0 : 0 ≤ 1 - Real.exp (-c) := by
    rw [sub_nonneg]; exact Real.exp_le_one_iff.2 (by linarith)
  exact hR'.trans (div_le_div₀ (hnum0.trans hnum) hnum hden0 hden)

/-- `log 20 ≤ 3`, used for the confidence level `1/20`. -/
theorem log_twenty_le_three : Real.log 20 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  calc (20 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
    _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num

/-- `log 160 ≤ 3 + 3 log 2`: the confidence `1/20` split over an 8-point grid. -/
theorem log_one_div_twenty_div_eight_le :
    Real.log (1 / (1 / 20 / 8)) ≤ 3 + 3 * 0.6931471808 := by
  rw [show (1 : ℝ) / (1 / 20 / 8) = 20 * 2 ^ 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := Real.log_two_lt_d9
  have := log_twenty_le_three
  push_cast
  linarith

/-- The deterministic step of the certificate: a sample on which the stated rational
inequalities hold, the empirical error of `c` is at most `q` and its population error exceeds `B`
lies in the Catoni bad event of `mlp_pacBayes`. The event does not depend on `t, q, γ, c', E, L, B`,
so the certificate holds uniformly over them. -/
theorem dirac_mem_badEvent (P : Population Observation) (a : Arch)
    (c : Code a.parameterCount 4) {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (T : Finset ℝ)
    {δ t q γ c' E L B : ℝ} (ht : t ∈ T) (ht0 : 0 < t)
    (hγ : Real.log (1 / (δ / T.card)) ≤ γ)
    (hc : t * q + (a.parameterCount * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) + γ) / n ≤ c')
    (hc0 : 0 ≤ c') (hE : Real.exp c' ≤ E) (hL : L ≤ Real.exp t) (hL1 : 1 < L)
    (hB : (1 - 1 / E) / (1 - 1 / L) ≤ B)
    {s : Fin n → Observation} (hemp : empRisk (classificationLoss a) s c ≤ q)
    (hrisk : B < P.risk (classificationLoss a c)) :
    s ∈ ⋃ t ∈ T, badEvent (classificationLoss a) P.law (centredPrior m c) n t (δ / T.card) := by
  rw [Set.mem_iUnion₂]
  refine ⟨t, ht, ?_⟩
  by_contra hgood
  have hnot : ¬ (t * n * expect (dirac c) (empRisk (classificationLoss a) s) +
      kl (dirac c) (centredPrior m c) + Real.log (1 / (δ / T.card)) <
      n * catoni t (expect (dirac c) (risk P.law (classificationLoss a)))) :=
    fun h => hgood ⟨dirac c, dirac_isDist c, h⟩
  rw [expect_dirac, expect_dirac, not_lt] at hnot
  have hkl := kl_dirac_centre_le hm c
  have hR := risk_mem (D := P.law) (classificationLoss_range a)
    (classificationLoss_measurable a) c
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : t * n * empRisk (classificationLoss a) s c ≤ t * n * q :=
    mul_le_mul_of_nonneg_left hemp (by positivity)
  have hcat : catoni t (risk P.law (classificationLoss a) c) ≤ c' := by
    refine le_trans (le_of_mul_le_mul_left ?_ hnR) hc
    have : (n : ℝ) * (t * q + (a.parameterCount * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) + γ) / n) =
        t * n * q + (a.parameterCount * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) + γ) := by
      field_simp
    rw [this]
    linarith
  have hfin := (risk_le_of_catoni ht0 hc0 hR hcat hE hL hL1).trans hB
  have hrisk' : B < risk P.law (classificationLoss a) c := hrisk
  linarith

/-- **Certificate for the prior centre.** If the reference code `c` was fixed
independently of the `n` IID bound observations, and the stated rational
inequalities hold, then with probability at least `1 - δ` the population error
of `c` is at most `B` whenever its empirical error is at most `q`. -/
theorem dirac_certificate (P : Population Observation) (a : Arch)
    (c : Code a.parameterCount 4) {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (T : Finset ℝ)
    (hT : T.Nonempty) {δ t q γ c' E L B : ℝ} (hδ : 0 < δ) (ht : t ∈ T) (ht0 : 0 < t)
    (hγ : Real.log (1 / (δ / T.card)) ≤ γ)
    (hc : t * q + (a.parameterCount * ((3 / 2 ^ m) / (1 - 3 / 2 ^ m)) + γ) / n ≤ c')
    (hc0 : 0 ≤ c') (hE : Real.exp c' ≤ E) (hL : L ≤ Real.exp t) (hL1 : 1 < L)
    (hB : (1 - 1 / E) / (1 - 1 / L) ≤ B) :
    sampleLaw P.law n {s | empRisk (classificationLoss a) s c ≤ q ∧
      B < P.risk (classificationLoss a c)} ≤ ENNReal.ofReal δ :=
  (measure_mono fun _ hs => dirac_mem_badEvent P a c hm hn T ht ht0 hγ hc hc0 hE hL hL1 hB
    hs.1 hs.2).trans (mlp_pacBayes P a c hm n T hT hδ)

end OpenTheory.QuantizedMLP
