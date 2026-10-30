import Theory.Learning.FiniteClass
import Models.QuantizedMLP.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Generalization certificates for finite codes and a quantized ReLU MLP

The population is an arbitrary probability law, the sample is IID, and the
learner may inspect the whole sample. All q^p parameter codes are charged.
No optimization, realizability, low-rank, or generalization premise is assumed.

This is the classical finite-class Hoeffding bound, not a new statistical rate.
The concrete decoder below describes a deterministic 16–4–10 ReLU network,
including biases, with 118 four-valued parameters. Its predictions use integers.
-/

open MeasureTheory StatLean.StatisticalLearning

namespace OpenTheory.QuantizedMLP

/-- Simultaneous population-risk control for every code. The codebook, decoder,
and loss must be fixed independently of the sample. -/
theorem uniform_code_tail {Z : Type*} [MeasurableSpace Z]
    (P : Population Z) {p q n : ℕ} (loss : Code p q → Z → ℝ)
    (hrange : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (loss h)) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    sampleLaw P.law n {s | ∃ h, empRisk loss s h + ε < P.risk (loss h)} ≤
      ENNReal.ofReal (2 * (q : ℝ) ^ p * Real.exp (-2 * n * ε ^ 2)) := by
  classical
  have h := finiteClass_measure_uniformDeviation_le (D := P.law) (ℓ := loss)
    (Finset.univ : Finset (Code p q)) (fun h _ => hrange h)
    (fun h _ => hmeas h) hn hε
  simp only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] at h
  refine (measure_mono ?_).trans h
  rintro s ⟨code, hbad⟩
  refine ⟨code, ?_⟩
  have habs := neg_le_abs (empRisk loss s code - P.risk (loss code))
  change ε < |empRisk loss s code - P.risk (loss code)|
  linarith

/-- Any data-dependent optimizer/selection rule inherits the same bound.
This is an outer-probability bound, so learner measurability is unnecessary. -/
theorem selected_code_tail {Z : Type*} [MeasurableSpace Z]
    (P : Population Z) {p q n : ℕ} (loss : Code p q → Z → ℝ)
    (hrange : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (loss h))
    (learner : (Fin n → Z) → Code p q) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    sampleLaw P.law n {s | empRisk loss s (learner s) + ε <
      P.risk (loss (learner s))} ≤
      ENNReal.ofReal (2 * (q : ℝ) ^ p * Real.exp (-2 * n * ε ^ 2)) := by
  apply (measure_mono ?_).trans (uniform_code_tail P loss hrange hmeas hn hε)
  intro s hs
  exact ⟨learner s, hs⟩

set_option maxRecDepth 4096 in
/-- Kernel-checked numerical constants, with no floating-point oracle. -/
theorem numerical_tail_le :
    2 * (4 : ℝ) ^ 118 * Real.exp (-2 * 1400 * (1 / 4 : ℝ) ^ 2) ≤ 1 / 20 := by
  have hlog : (242 : ℝ) * Real.log 2 ≤ 175 := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (2 : ℝ) ^ 242 ≤ Real.exp 175 := by
    calc
      (2 : ℝ) ^ 242 = Real.exp (242 * Real.log 2) := by
        simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
          (Real.exp_nat_mul (Real.log 2) 242).symm
      _ ≤ Real.exp 175 := Real.exp_le_exp.mpr hlog
  have hcoeff : (40 : ℝ) * 4 ^ 118 ≤ Real.exp 175 := by
    exact (by norm_num : (40 : ℝ) * 4 ^ 118 ≤ 2 ^ 242).trans hpow
  norm_num only [show (-2 * 1400 * (1 / 4 : ℝ) ^ 2) = -175 by norm_num]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos (175 : ℝ))).mpr
  nlinarith

/-- 95% confidence: a 236-bit model selected on 1400 IID examples has
population error at most empirical error plus 1/4. -/
theorem selected_code_certificate {Z : Type*} [MeasurableSpace Z]
    (P : Population Z) (loss : Code 118 4 → Z → ℝ)
    (hrange : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (loss h))
    (learner : (Fin 1400 → Z) → Code 118 4) :
    sampleLaw P.law 1400 {s | empRisk loss s (learner s) + 1 / 4 <
      P.risk (loss (learner s))} ≤ ENNReal.ofReal (1 / 20) := by
  exact (selected_code_tail P loss hrange hmeas learner (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 4)).trans (ENNReal.ofReal_le_ofReal numerical_tail_le)

-- Discrete observations include all integer input vectors, not just this dataset.
instance observationMeasurableSpace : MeasurableSpace Observation := ⊤

instance observationMeasurableSingletonClass : MeasurableSingletonClass Observation :=
  ⟨fun _ => trivial⟩

def classificationLoss (a : Arch) (code : Code a.parameterCount 4)
    (z : Observation) : ℝ := errorBit a code z

theorem classificationLoss_range (a : Arch)
    (code : Code a.parameterCount 4) (z : Observation) :
    classificationLoss a code z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold classificationLoss errorBit errorBitOfWeights
  split <;> norm_num

theorem classificationLoss_measurable (a : Arch)
    (code : Code a.parameterCount 4) :
    Measurable (classificationLoss a code) := measurable_of_countable _

/-- Actual ReLU inference, arbitrary architecture and data-dependent training.
The only architecture cost is the number of encoded parameters, including biases. -/
theorem mlp_tail (P : Population Observation) (a : Arch) {n : ℕ}
    (learner : (Fin n → Observation) → Code a.parameterCount 4)
    (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    sampleLaw P.law n {s | empRisk (classificationLoss a) s (learner s) + ε <
      P.risk (classificationLoss a (learner s))} ≤
      ENNReal.ofReal (2 * (4 : ℝ) ^ a.parameterCount *
        Real.exp (-2 * n * ε ^ 2)) :=
  selected_code_tail P _ (classificationLoss_range a)
    (classificationLoss_measurable a) learner hn hε

/-- The executable integer error count equals the empirical risk in the
probability theorem. This bridges the saved artifact to the statistical model. -/
theorem empiricalRisk_eq_errorCount (a : Arch)
    (code : Code a.parameterCount 4) (rows : List Observation) :
    empRisk (classificationLoss a) rows.get code =
      (errorCount a code rows : ℝ) / rows.length := by
  have hs : errorCount a code rows =
      ∑ i : Fin rows.length, errorBit a code (rows.get i) := by
    unfold errorCount errorCountOfWeights
    conv_lhs => rw [← List.ofFn_get rows, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hs, Nat.cast_sum]
  simp only [empRisk, classificationLoss, div_eq_mul_inv, mul_comm]

/-- The same bridge for a list re-indexed as a sample of a stated size. -/
theorem empiricalRisk_eq_errorCount_cast (a : Arch) (code : Code a.parameterCount 4)
    (rows : List Observation) {n : ℕ} (h : rows.length = n) :
    empRisk (classificationLoss a) (fun i : Fin n => rows.get (Fin.cast h.symm i)) code =
      (errorCount a code rows : ℝ) / n := by
  subst h
  exact empiricalRisk_eq_errorCount a code rows

/-- A network with at most 325 errors on 1400 observations receives the
48.22% certificate. The probability is over the training sample, not test labels. -/
theorem digits_certificate (P : Population Observation)
    (learner : (Fin 1400 → Observation) → Code digits16.parameterCount 4) :
    sampleLaw P.law 1400 {s |
      empRisk (classificationLoss digits16) s (learner s) ≤ 13 / 56 ∧
      27 / 56 < P.risk (classificationLoss digits16 (learner s))} ≤
      ENNReal.ofReal (1 / 20) := by
  apply (measure_mono ?_).trans (selected_code_certificate P _
    (classificationLoss_range digits16) (classificationLoss_measurable digits16) learner)
  rintro s ⟨hemp, hpop⟩
  change empRisk (classificationLoss digits16) s (learner s) + 1 / 4 <
    P.risk (classificationLoss digits16 (learner s))
  linarith

end OpenTheory.QuantizedMLP
