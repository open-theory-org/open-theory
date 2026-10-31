import StatLean.StatisticalLearning.Core.SampleLaw
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The exact binomial test-set bound (Clopper–Pearson)

Fix a hypothesis before seeing the sample, and a `{0,1}`-valued loss. Under
`n` IID draws, the number of errors `K` is exactly `Binomial(n, R)`, where `R`
is the population error (`sampleLaw_count_le`). Two consequences:

* **Test-set bound** (`testSet_bound`): if `P(Bin(n,p) ≤ k) ≤ δ`, then
  `P(K ≤ k ∧ p < R) ≤ δ`. This is the exact form of Langford's test-set bound.
* **Clopper–Pearson, uniform in the observed count** (`clopperPearson`):
  `P(F_R(K) ≤ δ) ≤ δ`, where `F_R` is the `Binomial(n, R)` distribution
  function. On a realized sample with at most `k` errors, `p < R` forces the
  sample into this event (`mem_clopperPearson_event`). So the certified rate
  may be read off the observed count; no threshold is fixed in advance.

The distribution is computed directly: the event `K ≤ k` is a disjoint union
of measurable cylinders, one per set of error positions, and each has product
probability `R^|A| (1-R)^(n-|A|)`. Monotonicity in `p` is the derivative
identity `d/dp P(Bin(n,p) ≤ k) = -n · b_{n-1,k}(p)` for Bernstein polynomials.

Unlike Catoni's bound, nothing here is paid for a temperature grid, a prior,
or simultaneity over posteriors. It applies only to one hypothesis fixed
independently of the sample.

References: the exact binomial (Clopper–Pearson) bound [@clopper1934use].
-/

noncomputable section
open MeasureTheory StatLean.StatisticalLearning Finset
open scoped Classical

namespace OpenTheory.BinomialTail

/-! ### The binomial distribution function -/

/-- `P(Bin(n, p) ≤ k)`. -/
def binomCdf (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ range (k + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

theorem binomCdf_nonneg (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binomCdf n k p :=
  sum_nonneg fun i _ => by have := hp.1; have : 0 ≤ 1 - p := by linarith [hp.2]
                           positivity

/-- More terms, more mass. -/
theorem binomCdf_mono {n k l : ℕ} (hkl : k ≤ l) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    binomCdf n k p ≤ binomCdf n l p := by
  have h1 : 0 ≤ 1 - p := by linarith [hp.2]
  have h0 := hp.1
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
    fun i _ _ => by positivity

theorem binomCdf_eq_eval (n k : ℕ) (p : ℝ) :
    binomCdf n k p = (∑ ν ∈ range (k + 1), bernsteinPolynomial ℝ n ν).eval p := by
  simp [binomCdf, bernsteinPolynomial, Polynomial.eval_finsetSum]

/-- `d/dp P(Bin(m+1, p) ≤ k) = -(m+1) b_{m,k}(p)`. -/
theorem derivative_sum_bernstein (m k : ℕ) :
    Polynomial.derivative (∑ ν ∈ range (k + 1), bernsteinPolynomial ℝ (m + 1) ν) =
      -((m : Polynomial ℝ) + 1) * bernsteinPolynomial ℝ m k := by
  induction k with
  | zero => simp [bernsteinPolynomial.derivative_zero]
  | succ k ih =>
    rw [sum_range_succ, Polynomial.derivative_add, ih, bernsteinPolynomial.derivative_succ_aux]
    ring

theorem binomCdf_zero (k : ℕ) (p : ℝ) : binomCdf 0 k p = 1 := by
  simp [binomCdf, sum_range_succ']

/-- The tail `P(Bin(n, p) ≤ k)` decreases in `p`. -/
theorem binomCdf_antitoneOn (n k : ℕ) : AntitoneOn (binomCdf n k) (Set.Icc 0 1) := by
  cases n with
  | zero => intro x _ y _ _; simp [binomCdf_zero]
  | succ m =>
    have hf : binomCdf (m + 1) k =
        fun p => (∑ ν ∈ range (k + 1), bernsteinPolynomial ℝ (m + 1) ν).eval p :=
      funext (binomCdf_eq_eval _ _)
    rw [hf]
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (Polynomial.continuousOn _)
      (Polynomial.differentiableOn _) fun x hx => ?_
    rw [interior_Icc] at hx
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    have h0 := hx.1.le
    rw [Polynomial.deriv, derivative_sum_bernstein]
    simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, neg_mul]
    exact neg_nonpos.2 (by positivity)

/-! ### Exact law of the error count -/

variable {Z : Type*} {n : ℕ}

/-- Positions of the sample that fall in `E`. -/
def hits (E : Set Z) (s : Sample Z n) : Finset (Fin n) := univ.filter fun i => s i ∈ E

/-- Number of sample points in `E`. -/
def count (E : Set Z) (s : Sample Z n) : ℕ := (hits E s).card

theorem count_le (E : Set Z) (s : Sample Z n) : count E s ≤ n := by
  simpa [count, hits] using card_filter_le (univ : Finset (Fin n)) fun i => s i ∈ E

/-- Samples whose hits are exactly `A`: a measurable rectangle. -/
def cylinder (E : Set Z) (A : Finset (Fin n)) : Set (Sample Z n) :=
  Set.univ.pi fun i => if i ∈ A then E else Eᶜ

theorem mem_cylinder {E : Set Z} {A : Finset (Fin n)} {s : Sample Z n} :
    s ∈ cylinder E A ↔ hits E s = A := by
  simp only [cylinder, Set.mem_pi, Set.mem_univ, true_imp_iff, Finset.ext_iff, hits, mem_filter,
    mem_univ, true_and]
  refine forall_congr' fun i => ?_
  split_ifs with h <;> simp [h]

theorem count_le_eq_iUnion (E : Set Z) (k : ℕ) :
    {s : Sample Z n | count E s ≤ k} =
      ⋃ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k), cylinder E A := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, mem_cylinder,
    exists_prop, count]
  exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨A, hA, rfl⟩; exact hA⟩

variable [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D]

theorem measureReal_cylinder {E : Set Z} (hE : MeasurableSet E) (A : Finset (Fin n)) :
    (sampleLaw D n).real (cylinder E A) = D.real E ^ A.card * (1 - D.real E) ^ (n - A.card) := by
  rw [measureReal_def, sampleLaw, cylinder, Measure.pi_pi, ENNReal.toReal_prod]
  have hc : D.real Eᶜ = 1 - D.real E := by rw [measureReal_compl hE, probReal_univ]
  have : ∀ i, (D (if i ∈ A then E else Eᶜ)).toReal = if i ∈ A then D.real E else 1 - D.real E :=
    fun i => by split_ifs; exacts [rfl, hc]
  simp only [this, prod_ite, prod_const, filter_mem_eq_inter, univ_inter]
  congr 2
  rw [show (univ.filter fun i => i ∉ A) = Aᶜ by ext; simp, card_compl, Fintype.card_fin]

theorem sum_subsets_card_le (R : ℝ) (k : ℕ) :
    ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      R ^ A.card * (1 - R) ^ (n - A.card) = binomCdf n k R := by
  set g : ℕ → ℝ := fun m => if m ≤ k then R ^ m * (1 - R) ^ (n - m) else 0
  have hL : ∑ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      R ^ A.card * (1 - R) ^ (n - A.card) =
        ∑ m ∈ range (n + k + 1), (n.choose m : ℝ) * g m := by
    rw [sum_filter, ← powerset_univ, sum_powerset_apply_card g, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    exact sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => by
      simp only [mem_range] at hm hm'
      simp [Nat.choose_eq_zero_of_lt (by omega : n < m)]
  have hR : binomCdf n k R = ∑ m ∈ range (n + k + 1), (n.choose m : ℝ) * g m := by
    rw [binomCdf]
    refine sum_subset_zero_on_sdiff (range_subset_range.2 (by omega)) (fun m hm => ?_)
      (fun m hm => ?_)
    · simp only [mem_sdiff, mem_range] at hm
      simp [g, show ¬ m ≤ k by omega]
    · simp only [mem_range] at hm
      simp [g, show m ≤ k by omega, mul_assoc]
  rw [hL, hR]

/-- **The error count is binomial.** For IID draws, `P(#{i | sᵢ ∈ E} ≤ k)` is
the `Binomial(n, D E)` distribution function at `k`. -/
theorem sampleLaw_count_le {E : Set Z} (hE : MeasurableSet E) (k : ℕ) :
    sampleLaw D n {s | count E s ≤ k} = ENNReal.ofReal (binomCdf n k (D.real E)) := by
  have hd : Set.PairwiseDisjoint
      (↑((univ : Finset (Finset (Fin n))).filter fun A => A.card ≤ k)) (cylinder (n := n) E) :=
    fun A _ B _ hAB => Set.disjoint_left.2 fun s hA hB =>
      hAB ((mem_cylinder.1 hA).symm.trans (mem_cylinder.1 hB))
  have hm : ∀ A ∈ (univ : Finset (Finset (Fin n))).filter (fun A => A.card ≤ k),
      MeasurableSet (cylinder E A) := fun A _ =>
    MeasurableSet.univ_pi fun i => by
      split_ifs
      exacts [hE, hE.compl]
  rw [← ofReal_measureReal, count_le_eq_iUnion, measureReal_biUnion_finset hd hm]
  simp only [measureReal_cylinder hE, sum_subsets_card_le]

/-! ### The test-set bounds -/

theorem measureReal_mem_Icc (E : Set Z) : D.real E ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- **Exact test-set bound.** If `P(Bin(n,p) ≤ k) ≤ δ`, then with probability at
least `1 - δ` it is not the case that at most `k` points fall in `E` while
`D E > p`. -/
theorem count_testSet_bound {E : Set Z} (hE : MeasurableSet E) {k : ℕ} {p δ : ℝ} (hp : 0 ≤ p)
    (hcdf : binomCdf n k p ≤ δ) :
    sampleLaw D n {s | count E s ≤ k ∧ p < D.real E} ≤ ENNReal.ofReal δ := by
  by_cases hpR : p < D.real E
  · have hR := measureReal_mem_Icc (D := D) E
    calc sampleLaw D n {s | count E s ≤ k ∧ p < D.real E}
        = sampleLaw D n {s | count E s ≤ k} := by simp [hpR]
      _ = ENNReal.ofReal (binomCdf n k (D.real E)) := sampleLaw_count_le hE k
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal <|
          (binomCdf_antitoneOn n k ⟨hp, hpR.le.trans hR.2⟩ hR hpR.le).trans hcdf
  · simp [hpR]

/-- **Clopper–Pearson, uniform in the observed count.** With probability at
least `1 - δ`, the observed count is not in the lower `δ`-tail of
`Binomial(n, D E)`. -/
theorem count_clopperPearson {E : Set Z} (hE : MeasurableSet E) (δ : ℝ) :
    sampleLaw D n {s | binomCdf n (count E s) (D.real E) ≤ δ} ≤ ENNReal.ofReal δ := by
  set R := D.real E
  set S := (range (n + 1)).filter fun k => binomCdf n k R ≤ δ
  rcases S.eq_empty_or_nonempty with hS | hS
  · have : {s : Sample Z n | binomCdf n (count E s) R ≤ δ} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have : count E s ∈ S := mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (count_le E s)), h⟩
      simp [hS] at this
    simp [this]
  · have hmax := mem_filter.1 (S.max'_mem hS)
    calc sampleLaw D n {s | binomCdf n (count E s) R ≤ δ}
        ≤ sampleLaw D n {s | count E s ≤ S.max' hS} := measure_mono fun s h =>
          S.le_max' _ (mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (count_le E s)), h⟩)
      _ = ENNReal.ofReal (binomCdf n (S.max' hS) R) := sampleLaw_count_le hE _
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hmax.2

/-- Reading the bound off a realized sample: if it has at most `k` points in `E`,
`P(Bin(n,p) ≤ k) ≤ δ` and `D E > p`, it lies in the event of `count_clopperPearson`. -/
theorem mem_count_clopperPearson_event {E : Set Z} {s : Sample Z n} {k : ℕ} {p δ : ℝ}
    (hk : count E s ≤ k) (hp : 0 ≤ p) (hcdf : binomCdf n k p ≤ δ) (hpR : p < D.real E) :
    s ∈ {s : Sample Z n | binomCdf n (count E s) (D.real E) ≤ δ} := by
  have hR := measureReal_mem_Icc (D := D) E
  exact ((binomCdf_mono hk hR).trans
    (binomCdf_antitoneOn n k ⟨hp, hpR.le.trans hR.2⟩ hR hpR.le)).trans hcdf

/-! ### `{0,1}` losses -/

variable {H : Type*} {ℓ : H → Z → ℝ} {h : H}

/-- Number of sample points on which hypothesis `h` errs. -/
def numErrors (ℓ : H → Z → ℝ) (s : Sample Z n) (h : H) : ℕ := count {z | ℓ h z = 1} s

theorem measurableSet_errors (hmeas : Measurable (ℓ h)) : MeasurableSet {z | ℓ h z = 1} :=
  hmeas (measurableSet_singleton 1)

omit [MeasurableSpace Z] [IsProbabilityMeasure D] in
theorem loss_eq_indicator (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) :
    ℓ h = Set.indicator {z | ℓ h z = 1} 1 := by
  funext z
  rcases h01 z with hz | hz <;> simp [Set.indicator, hz]

omit [IsProbabilityMeasure D] in
/-- The risk of a `{0,1}` loss is the probability of the error set. -/
theorem risk_eq_measureReal (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h)) :
    risk D ℓ h = D.real {z | ℓ h z = 1} := by
  rw [risk]
  conv_lhs => rw [loss_eq_indicator h01]
  exact integral_indicator_one (measurableSet_errors hmeas)

omit [MeasurableSpace Z] [IsProbabilityMeasure D] in
/-- The empirical risk of a `{0,1}` loss is the error count over `n`. -/
theorem numErrors_eq (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (s : Sample Z n) :
    (numErrors ℓ s h : ℝ) = n * empRisk ℓ s h := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [numErrors, count, hits, univ_eq_empty]
  have hsum : ∑ i, ℓ h (s i) = numErrors ℓ s h := by
    rw [numErrors, count, hits, ← sum_boole]
    exact sum_congr rfl fun i _ => by rcases h01 (s i) with hz | hz <;> simp [hz]
  rw [empRisk, ← hsum, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Test-set bound for a fixed classifier.** If `P(Bin(n,p) ≤ k) ≤ δ` and
`n q ≤ k`, then with probability at least `1 - δ` over `n` IID observations,
empirical error at most `q` implies population error at most `p`. -/
theorem testSet_bound (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h))
    {k : ℕ} {p q δ : ℝ} (hp : 0 ≤ p) (hq : n * q ≤ k) (hcdf : binomCdf n k p ≤ δ) :
    sampleLaw D n {s | empRisk ℓ s h ≤ q ∧ p < risk D ℓ h} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun s hs => ?_).trans
    (count_testSet_bound (D := D) (measurableSet_errors hmeas) hp hcdf)
  obtain ⟨hemp, hrisk⟩ := hs
  rw [risk_eq_measureReal (D := D) h01 hmeas] at hrisk
  refine ⟨?_, hrisk⟩
  have : (numErrors ℓ s h : ℝ) ≤ k := by
    rw [numErrors_eq h01]
    exact (mul_le_mul_of_nonneg_left hemp (Nat.cast_nonneg n)).trans hq
  exact_mod_cast this

/-- **Clopper–Pearson for a fixed classifier**, uniform in the observed count. -/
theorem clopperPearson (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h)) (δ : ℝ) :
    sampleLaw D n {s | binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ} ≤ ENNReal.ofReal δ := by
  rw [risk_eq_measureReal h01 hmeas]
  exact count_clopperPearson (measurableSet_errors hmeas) δ

/-- A realized sample with at most `k` errors on which the population error
exceeds `p` lies in the `δ`-event of `clopperPearson`. -/
theorem mem_clopperPearson_event (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h))
    {s : Sample Z n} {k : ℕ} {p δ : ℝ} (hk : numErrors ℓ s h ≤ k) (hp : 0 ≤ p)
    (hcdf : binomCdf n k p ≤ δ) (hpR : p < risk D ℓ h) :
    s ∈ {s : Sample Z n | binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ} := by
  rw [risk_eq_measureReal h01 hmeas] at hpR ⊢
  exact mem_count_clopperPearson_event hk hp hcdf hpR

/-! ### Exact rational evaluation -/

/-- Numerator of `P(Bin(n, a/b) ≤ k) · b^n`, with linear-time binomial
coefficients so that the kernel can evaluate it. -/
def tailNumerator (n k a b : ℕ) : ℕ :=
  ((List.range (k + 1)).map fun i =>
    n.descFactorial i / i.factorial * a ^ i * (b - a) ^ (n - i)).sum

theorem tailNumerator_eq (n k a b : ℕ) :
    tailNumerator n k a b = ∑ i ∈ range (k + 1), n.choose i * a ^ i * (b - a) ^ (n - i) := by
  rw [tailNumerator]
  induction k with
  | zero => simp [Nat.choose_eq_descFactorial_div_factorial]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ (n := k + 1),
      Nat.choose_eq_descFactorial_div_factorial n (k + 1)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem binomCdf_div_eq (n k : ℕ) {a b : ℕ} (hab : a ≤ b) (hb : 0 < b) :
    binomCdf n k ((a : ℝ) / b) = (tailNumerator n k a b : ℝ) / (b : ℝ) ^ n := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [tailNumerator_eq, binomCdf, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun i _ => ?_
  rcases le_or_gt i n with hi | hi
  · have hsub : (1 : ℝ) - a / b = ((b - a : ℕ) : ℝ) / b := by
      rw [Nat.cast_sub hab]; field_simp
    rw [hsub, div_pow, div_pow, show (b : ℝ) ^ n = (b : ℝ) ^ i * (b : ℝ) ^ (n - i) by
      rw [← pow_add, Nat.add_sub_cancel' hi]]
    push_cast
    field_simp
  · simp [Nat.choose_eq_zero_of_lt hi]

end OpenTheory.BinomialTail
