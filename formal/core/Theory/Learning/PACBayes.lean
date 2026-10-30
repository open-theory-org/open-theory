import StatLean.StatisticalLearning.Core.SampleLaw
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Catoni's PAC-Bayes bound on a finite hypothesis space

Let `D` be any probability law, draw `n` IID observations, and fix a loss in
`[0,1]` and a full-support prior `π` on a finite hypothesis space before seeing
the sample. With probability at least `1 - δ`, simultaneously for every
posterior `Q` (which may depend on the sample),

  `n Φ_t(R(Q)) ≤ t n R̂(Q) + KL(Q ‖ π) + log (1/δ)`,  `Φ_t(p) = -log (1 - (1 - e^{-t}) p)`.

Here `R(Q)` and `R̂(Q)` are the population and empirical risks of the Gibbs
predictor that draws `h ∼ Q` per prediction. Optimising over `t` recovers the
binary-kl (Seeger–Maurer) bound, since `sup_t (Φ_t(p) - t q) = kl(q ‖ p)` for
`q ≤ p`; `catoni_grid` pays `log |T|` for choosing `t` from a finite grid.

The proof is the classical one (Catoni 2007, Thm 1.2.6): convexity of `exp`
gives the exponential moment, Markov bounds it, and the Donsker–Varadhan
inequality (here a finite Jensen inequality for `log`) transfers it to every
`Q` at once. A point-mass posterior gives the Occam bound with code length
`log (1/π h)`; this includes the finite-class theorem with a uniform prior.
-/

noncomputable section
open MeasureTheory StatLean.StatisticalLearning

namespace OpenTheory.PACBayes

variable {Z H : Type*} [MeasurableSpace Z] [Fintype H]

/-- Catoni's convex link `Φ_t(p) = -log (1 - (1 - e^{-t}) p)`. -/
def catoni (t p : ℝ) : ℝ := -Real.log (1 - (1 - Real.exp (-t)) * p)

/-- A probability vector on the finite hypothesis space. -/
structure IsDist (Q : H → ℝ) : Prop where
  nonneg : ∀ h, 0 ≤ Q h
  sum_eq_one : ∑ h, Q h = 1

/-- Expectation of `f` under the weights `Q`. -/
def expect (Q f : H → ℝ) : ℝ := ∑ h, Q h * f h

/-- Relative entropy `KL(Q ‖ π)`, with `0 log 0 = 0`. Meaningful when `π > 0`. -/
def kl (Q π : H → ℝ) : ℝ := ∑ h, Q h * Real.log (Q h / π h)

/-! ### The link function -/

theorem catoni_base_pos (t : ℝ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - (1 - Real.exp (-t)) * p := by
  have he := Real.exp_pos (-t)
  rcases le_total 0 (1 - Real.exp (-t)) with ha | ha <;> nlinarith [hp.1, hp.2]

theorem catoni_convexOn (t : ℝ) : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (catoni t) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (catoni_base_pos t hx))
    (Set.mem_Ioi.2 (catoni_base_pos t hy)) ha hb hab
  simp only [smul_eq_mul, catoni] at hc ⊢
  have hlin : a * (1 - (1 - Real.exp (-t)) * x) + b * (1 - (1 - Real.exp (-t)) * y) =
      1 - (1 - Real.exp (-t)) * (a * x + b * y) := by linear_combination hab
  rw [hlin] at hc
  linarith

/-- Inverting the link: a bound on `Φ_t(p)` is a bound on `p`. -/
theorem catoni_le_iff {t p c : ℝ} (ht : 0 < t) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    catoni t p ≤ c ↔ p ≤ (1 - Real.exp (-c)) / (1 - Real.exp (-t)) := by
  have hk : 0 < 1 - Real.exp (-t) := by
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [catoni, neg_le, Real.le_log_iff_exp_le (catoni_base_pos t hp), le_div_iff₀ hk]
  constructor <;> intro h <;> linarith

/-! ### Exponential moment of a single hypothesis -/

/-- Convexity of `exp`: a `[0,1]` variable is dominated by a Bernoulli one. -/
theorem exp_neg_mul_le (t : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-t * x) ≤ 1 - (1 - Real.exp (-t)) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-t))
    (sub_nonneg.2 hx.2) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (-t * x) = Real.exp (x * -t) := by ring_nf
    _ ≤ 1 - x + x * Real.exp (-t) := h
    _ = 1 - (1 - Real.exp (-t)) * x := by ring

variable {D : Measure Z} [IsProbabilityMeasure D] {ℓ : H → Z → ℝ}

omit [Fintype H] in
theorem loss_integrable (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (h : H) : Integrable (ℓ h) D :=
  Integrable.of_bound (hmeas h).aestronglyMeasurable 1 (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hrange h z).1, (hrange h z).2])

omit [Fintype H] in
theorem risk_mem (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (h : H) : risk D ℓ h ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun z => (hrange h z).1, ?_⟩
  calc risk D ℓ h ≤ ∫ _, (1 : ℝ) ∂D :=
        integral_mono (loss_integrable hrange hmeas h) (integrable_const 1)
          fun z => (hrange h z).2
    _ = 1 := by simp

omit [Fintype H] in
theorem mgf_le (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (t : ℝ) (h : H) :
    ∫ z, Real.exp (-t * ℓ h z) ∂D ≤ 1 - (1 - Real.exp (-t)) * risk D ℓ h := by
  have hlin : Integrable (fun z => 1 - (1 - Real.exp (-t)) * ℓ h z) D :=
    (integrable_const 1).sub ((loss_integrable hrange hmeas h).const_mul _)
  have hexp : Integrable (fun z => Real.exp (-t * ℓ h z)) D :=
    hlin.mono' (((hmeas h).const_mul (-t)).exp.aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact exp_neg_mul_le t (hrange h z))
  calc ∫ z, Real.exp (-t * ℓ h z) ∂D ≤ ∫ z, (1 - (1 - Real.exp (-t)) * ℓ h z) ∂D :=
        integral_mono hexp hlin fun z => exp_neg_mul_le t (hrange h z)
    _ = 1 - (1 - Real.exp (-t)) * risk D ℓ h := by
        rw [integral_sub (integrable_const 1) ((loss_integrable hrange hmeas h).const_mul _),
          integral_const_mul]
        simp [risk]

omit [MeasurableSpace Z] [Fintype H] in
theorem sum_loss_mem (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1) {n : ℕ}
    (s : Sample Z n) (h : H) : ∑ i, ℓ h (s i) ∈ Set.Icc (0 : ℝ) n := by
  refine ⟨Finset.sum_nonneg fun i _ => (hrange h (s i)).1, ?_⟩
  calc ∑ i, ℓ h (s i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hrange h (s i)).2
    _ = n := by simp

omit [MeasurableSpace Z] [Fintype H] in
theorem natCast_mul_empRisk {n : ℕ} (s : Sample Z n) (h : H) :
    (n : ℝ) * empRisk ℓ s h = ∑ i, ℓ h (s i) := by
  unfold empRisk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

omit [Fintype H] in
theorem exp_moment_integrable (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (n : ℕ) (c t : ℝ) (h : H) :
    Integrable (fun s : Sample Z n => Real.exp (c - t * ∑ i, ℓ h (s i)))
      (sampleLaw D n) := by
  refine Integrable.of_bound ?_ (Real.exp (c + |t| * n)) (ae_of_all _ fun s => ?_)
  · exact (measurable_const.sub (measurable_const.mul (Finset.measurable_sum _
      fun i _ => (hmeas h).comp (measurable_pi_apply i)))).exp.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have hs := sum_loss_mem hrange s h
    have : -(t * ∑ i, ℓ h (s i)) ≤ |t| * n := by
      calc -(t * ∑ i, ℓ h (s i)) ≤ |t * ∑ i, ℓ h (s i)| := neg_le_abs _
        _ = |t| * ∑ i, ℓ h (s i) := by rw [abs_mul, abs_of_nonneg hs.1]
        _ ≤ |t| * n := mul_le_mul_of_nonneg_left hs.2 (abs_nonneg t)
    linarith

omit [Fintype H] in
/-- The IID exponential moment: `E exp(n Φ_t(R) - t Σ ℓ) ≤ 1` for every `t`. -/
theorem exp_moment_le (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (n : ℕ) (t : ℝ) (h : H) :
    ∫ s, Real.exp (n * catoni t (risk D ℓ h) - t * ∑ i, ℓ h (s i)) ∂(sampleLaw D n) ≤ 1 := by
  set b := 1 - (1 - Real.exp (-t)) * risk D ℓ h with hb_def
  have hb : 0 < b := catoni_base_pos t (risk_mem hrange hmeas h)
  have hsplit : (fun s : Sample Z n =>
      Real.exp (n * catoni t (risk D ℓ h) - t * ∑ i, ℓ h (s i))) =
      fun s => Real.exp (n * catoni t (risk D ℓ h)) * ∏ i, Real.exp (-t * ℓ h (s i)) := by
    funext s
    rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
    ring_nf
  rw [hsplit, integral_const_mul, sampleLaw,
    integral_fintype_prod_eq_pow (fun z => Real.exp (-t * ℓ h z)), Fintype.card_fin]
  have hpow : (∫ z, Real.exp (-t * ℓ h z) ∂D) ^ n ≤ b ^ n :=
    pow_le_pow_left₀ (integral_nonneg fun _ => (Real.exp_pos _).le)
      (mgf_le hrange hmeas t h) n
  have hone : Real.exp (n * catoni t (risk D ℓ h)) * b ^ n = 1 := by
    rw [catoni, ← hb_def, ← Real.exp_log hb, ← Real.exp_nat_mul, ← Real.exp_add,
      Real.log_exp]
    simp
  calc Real.exp (n * catoni t (risk D ℓ h)) * (∫ z, Real.exp (-t * ℓ h z) ∂D) ^ n
      ≤ Real.exp (n * catoni t (risk D ℓ h)) * b ^ n :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = 1 := hone

/-! ### Change of measure -/

/-- Donsker–Varadhan for finite spaces: `E_Q f ≤ KL(Q ‖ π) + log E_π e^f`. -/
theorem expect_le_kl_add_log (Q π f : H → ℝ) (hQ : IsDist Q) (hπ : ∀ h, 0 < π h) :
    expect Q f ≤ kl Q π + Real.log (∑ h, π h * Real.exp (f h)) := by
  classical
  set S := Finset.univ.filter fun h => 0 < Q h
  have hpos : ∀ h, Q h ≠ 0 → 0 < Q h := fun h hne => lt_of_le_of_ne (hQ.nonneg h) hne.symm
  have hS : ∑ h ∈ S, Q h = 1 := by
    rw [Finset.sum_filter_of_ne fun h _ hne => hpos h hne, hQ.sum_eq_one]
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty] at hS
    exact zero_ne_one hS
  set p : H → ℝ := fun h => π h * Real.exp (f h) / Q h
  have hgap : expect Q f - kl Q π = ∑ h ∈ S, Q h * Real.log (p h) := by
    rw [expect, kl, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_filter_of_ne (p := fun h => 0 < Q h) fun h _ hne => by
      refine hpos h fun hq => hne ?_
      simp [hq]]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hq := (Finset.mem_filter.1 hh).2
    simp only [p]
    rw [Real.log_div (mul_pos (hπ h) (Real.exp_pos _)).ne' hq.ne', Real.log_mul (hπ h).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_div hq.ne' (hπ h).ne']
    ring
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := S) (w := Q) (p := p)
    (fun h _ => hQ.nonneg h) hS fun h hh => by
      have hq := (Finset.mem_filter.1 hh).2
      exact Set.mem_Ioi.2 (by simp only [p]; have := hπ h; positivity)
  simp only [smul_eq_mul] at hjensen
  have hcancel : ∑ h ∈ S, Q h * p h = ∑ h ∈ S, π h * Real.exp (f h) :=
    Finset.sum_congr rfl fun h hh => by
      simp only [p]; field_simp [(Finset.mem_filter.1 hh).2.ne']
  rw [hcancel] at hjensen
  have hSpos : 0 < ∑ h ∈ S, π h * Real.exp (f h) :=
    Finset.sum_pos (fun h _ => by have := hπ h; positivity) hSne
  have hsub : ∑ h ∈ S, π h * Real.exp (f h) ≤ ∑ h, π h * Real.exp (f h) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      fun h _ _ => by have := hπ h; positivity
  have := Real.log_le_log hSpos hsub
  linarith

/-! ### The PAC-Bayes theorem -/

/-- The sample-dependent bad event: some posterior violates Catoni's inequality. -/
def badEvent (ℓ : H → Z → ℝ) (D : Measure Z) (π : H → ℝ) (n : ℕ) (t δ : ℝ) :
    Set (Sample Z n) :=
  {s | ∃ Q, IsDist Q ∧ t * n * expect Q (empRisk ℓ s) + kl Q π + Real.log (1 / δ) <
    n * catoni t (expect Q (risk D ℓ))}

/-- **Catoni's PAC-Bayes bound.** For every `t`, with probability at least `1 - δ`
over the IID sample, every posterior satisfies the Catoni inequality. -/
theorem catoni_pacBayes (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) {π : H → ℝ} (hπ : ∀ h, 0 < π h)
    (hπ1 : ∑ h, π h = 1) (n : ℕ) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    sampleLaw D n (badEvent ℓ D π n t δ) ≤ ENNReal.ofReal δ := by
  set g : H → Sample Z n → ℝ := fun h s =>
    Real.exp (n * catoni t (risk D ℓ h) - t * ∑ i, ℓ h (s i))
  set F : Sample Z n → ℝ := fun s => ∑ h, π h * g h s
  have hgint : ∀ h, Integrable (g h) (sampleLaw D n) := fun h =>
    exp_moment_integrable hrange hmeas n _ t h
  have hFint : Integrable F (sampleLaw D n) :=
    integrable_finsetSum _ fun h _ => (hgint h).const_mul _
  have hne : (Finset.univ : Finset H).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hπ1
  have hFpos : ∀ s, 0 < F s := fun s =>
    Finset.sum_pos (fun h _ => mul_pos (hπ h) (Real.exp_pos _)) hne
  have hFle : ∫ s, F s ∂(sampleLaw D n) ≤ 1 := by
    rw [integral_finsetSum _ fun h _ => (hgint h).const_mul _]
    calc ∑ h, ∫ s, π h * g h s ∂(sampleLaw D n) = ∑ h, π h * ∫ s, g h s ∂(sampleLaw D n) :=
          Finset.sum_congr rfl fun h _ => integral_const_mul _ _
      _ ≤ ∑ h, π h * 1 := Finset.sum_le_sum fun h _ =>
          mul_le_mul_of_nonneg_left (exp_moment_le hrange hmeas n t h) (hπ h).le
      _ = 1 := by simp [hπ1]
  -- every bad sample has a large exponential moment
  have hsub : badEvent ℓ D π n t δ ⊆ {s | 1 / δ ≤ F s} := by
    rintro s ⟨Q, hQ, hbad⟩
    have hjensen : catoni t (expect Q (risk D ℓ)) ≤ expect Q fun h => catoni t (risk D ℓ h) := by
      simpa [expect, smul_eq_mul] using (catoni_convexOn t).map_sum_le (t := Finset.univ)
        (w := Q) (p := risk D ℓ) (fun h _ => hQ.nonneg h) hQ.sum_eq_one
        fun h _ => risk_mem hrange hmeas h
    have hdv := expect_le_kl_add_log Q π
      (fun h => n * catoni t (risk D ℓ h) - t * ∑ i, ℓ h (s i)) hQ hπ
    have hsplit : expect Q (fun h => n * catoni t (risk D ℓ h) - t * ∑ i, ℓ h (s i)) =
        n * expect Q (fun h => catoni t (risk D ℓ h)) - t * n * expect Q (empRisk ℓ s) := by
      unfold expect
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      beta_reduce
      rw [← natCast_mul_empRisk s h]
      ring
    have hlog : Real.log (1 / δ) < Real.log (F s) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := mul_le_mul_of_nonneg_left hjensen hn
      linarith
    exact (Real.log_lt_log_iff (by positivity) (hFpos s)).1 hlog |>.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun s => (hFpos s).le) hFint (1 / δ)
  have hreal : (sampleLaw D n).real {s | 1 / δ ≤ F s} ≤ δ := by
    have h1 : 1 / δ * (sampleLaw D n).real {s | 1 / δ ≤ F s} ≤ 1 := hmarkov.trans hFle
    rw [div_mul_eq_mul_div, one_mul, div_le_one hδ] at h1
    exact h1
  calc sampleLaw D n (badEvent ℓ D π n t δ) ≤ sampleLaw D n {s | 1 / δ ≤ F s} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((sampleLaw D n).real {s | 1 / δ ≤ F s}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

/-- Choosing `t` after seeing the data from a finite grid costs `log |T|`. -/
theorem catoni_grid (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) {π : H → ℝ} (hπ : ∀ h, 0 < π h)
    (hπ1 : ∑ h, π h = 1) (n : ℕ) (T : Finset ℝ) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    sampleLaw D n (⋃ t ∈ T, badEvent ℓ D π n t (δ / T.card)) ≤ ENNReal.ofReal δ := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  calc sampleLaw D n (⋃ t ∈ T, badEvent ℓ D π n t (δ / T.card))
      ≤ ∑ t ∈ T, sampleLaw D n (badEvent ℓ D π n t (δ / T.card)) :=
        measure_biUnion_finset_le T _
    _ ≤ ∑ _t ∈ T, ENNReal.ofReal (δ / T.card) := Finset.sum_le_sum fun t _ =>
        catoni_pacBayes hrange hmeas hπ hπ1 n t (by positivity)
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Finset.sum_const,
          nsmul_eq_mul, mul_div_cancel₀ _ hc.ne']

/-! ### Point-mass posteriors: the Occam bound -/

/-- The point mass at `h`. -/
def dirac [DecidableEq H] (h : H) : H → ℝ := fun g => if g = h then 1 else 0

theorem dirac_isDist [DecidableEq H] (h : H) : IsDist (dirac h) :=
  ⟨fun g => by unfold dirac; split <;> norm_num, by simp [dirac]⟩

theorem expect_dirac [DecidableEq H] (h : H) (f : H → ℝ) : expect (dirac h) f = f h := by
  simp [expect, dirac]

theorem kl_dirac [DecidableEq H] (h : H) (π : H → ℝ) :
    kl (dirac h) π = Real.log (1 / π h) := by
  simp [kl, dirac]

/-- **Occam bound** for an arbitrary data-dependent learner: the code length
`log (1/π h)` of the selected hypothesis replaces `log |H|`. -/
theorem occam_catoni [DecidableEq H] (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) {π : H → ℝ} (hπ : ∀ h, 0 < π h)
    (hπ1 : ∑ h, π h = 1) {n : ℕ} (learner : Sample Z n → H) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    sampleLaw D n {s | t * n * empRisk ℓ s (learner s) + Real.log (1 / π (learner s)) +
      Real.log (1 / δ) < n * catoni t (risk D ℓ (learner s))} ≤ ENNReal.ofReal δ := by
  refine (measure_mono ?_).trans (catoni_pacBayes hrange hmeas hπ hπ1 n t hδ)
  intro s hs
  refine ⟨dirac (learner s), dirac_isDist _, ?_⟩
  rwa [expect_dirac, expect_dirac, kl_dirac]

end OpenTheory.PACBayes
