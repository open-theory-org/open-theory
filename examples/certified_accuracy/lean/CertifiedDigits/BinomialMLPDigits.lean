import CertifiedDigits.PACBayesMLPDigits
import Foundations.Probability.BinomialTail

/-! # Exact binomial certificate for the 64–16–10 two-bit MLP on held-out digits

Same saved network, same 397 held-out rows (16 errors, checked by kernel
reduction in `PACBayesMLPDigits`) and same confidence `δ = 1/20` as the
PAC-Bayes certificate. Catoni's bound is replaced by the exact binomial tail,
which needs no prior, temperature grid or simultaneity over posteriors: the
network is a single hypothesis fixed before the held-out rows were used.

`P(Bin(397, 303/5000) ≤ 16) ≤ 1/20` is checked as an integer inequality by the
kernel. The exact Clopper–Pearson value for 16/397 is 6.0571%; 6.06% is its
four-digit rounding up. -/

namespace OpenTheory.BinomialMLPDigits
open MeasureTheory StatLean.StatisticalLearning OpenTheory.QuantizedMLP OpenTheory.BinomialTail
  OpenTheory.PACBayesMLPDigits

theorem classificationLoss_zero_or_one (a : Arch) (c : Code a.parameterCount 4) (z : Observation) :
    classificationLoss a c z = 0 ∨ classificationLoss a c z = 1 := by
  unfold classificationLoss errorBit errorBitOfWeights
  split <;> simp

/-- `20 · 5000^397 · P(Bin(397, 303/5000) ≤ 16) ≤ 5000^397`, in integers. -/
theorem tailNumerator_le : 20 * tailNumerator 397 16 303 5000 ≤ 5000 ^ 397 := by decide +kernel

theorem binomCdf_le : binomCdf 397 16 (303 / 5000) ≤ 1 / 20 := by
  have h := (Nat.cast_le (α := ℝ)).2 tailNumerator_le
  rw [Nat.cast_mul, Nat.cast_pow] at h
  have hp : (303 / 5000 : ℝ) = ((303 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ) := by norm_num
  rw [hp, binomCdf_div_eq _ _ (by norm_num) (by norm_num), div_le_iff₀ (by positivity)]
  generalize ((5000 : ℕ) : ℝ) ^ 397 = B at h ⊢
  push_cast at h
  linarith

theorem heldout_numErrors : numErrors (classificationLoss arch) heldoutSample network = 16 := by
  have h := numErrors_eq (classificationLoss_zero_or_one arch network) heldoutSample
  rw [heldout_empirical_error] at h
  have h16 : (numErrors (classificationLoss arch) heldoutSample network : ℝ) = 16 := by
    rw [h]; norm_num
  exact_mod_cast h16

/-- **Test-set certificate.** With probability at least 95% over 397 IID held-out
observations, if the saved network makes at most 16 errors on them then its
population error is at most 6.06%. Same event as `heldout_certificate`, whose
bound is 7.99%. -/
theorem heldout_testSet_certificate (P : Population Observation) :
    sampleLaw P.law 397 {s | empRisk (classificationLoss arch) s network ≤ (16 / 397 : ℝ) ∧
      (303 / 5000 : ℝ) < P.risk (classificationLoss arch network)} ≤ ENNReal.ofReal (1 / 20) :=
  testSet_bound (k := 16) (classificationLoss_zero_or_one arch network)
    (classificationLoss_measurable arch network) (by norm_num) (by norm_num) binomCdf_le

/-- The realized held-out sample lies in the 5% failure event exactly when the
saved network's population error exceeds 6.06%. -/
theorem heldoutSample_fails_iff (P : Population Observation) :
    heldoutSample ∈ {s | empRisk (classificationLoss arch) s network ≤ (16 / 397 : ℝ) ∧
      (303 / 5000 : ℝ) < P.risk (classificationLoss arch network)} ↔
      (303 / 5000 : ℝ) < P.risk (classificationLoss arch network) := by
  simp [heldout_empirical_error]

/-- **Clopper–Pearson, with no threshold fixed in advance.** With probability at
least 95% over 397 IID held-out observations, the observed error count is not
in the lower 5% tail of `Binomial(397, R)`, where `R` is the population error. -/
theorem heldout_clopperPearson (P : Population Observation) :
    sampleLaw P.law 397 {s | binomCdf 397 (numErrors (classificationLoss arch) s network)
      (P.risk (classificationLoss arch network)) ≤ 1 / 20} ≤ ENNReal.ofReal (1 / 20) :=
  clopperPearson (classificationLoss_zero_or_one arch network)
    (classificationLoss_measurable arch network) _

/-- If the population error exceeds 6.06%, the realized held-out sample is in the
5% event of `heldout_clopperPearson`. -/
theorem heldoutSample_fails_of_risk_gt (P : Population Observation)
    (h : (303 / 5000 : ℝ) < P.risk (classificationLoss arch network)) :
    heldoutSample ∈ {s | binomCdf 397 (numErrors (classificationLoss arch) s network)
      (P.risk (classificationLoss arch network)) ≤ 1 / 20} :=
  mem_clopperPearson_event (classificationLoss_zero_or_one arch network)
    (classificationLoss_measurable arch network) heldout_numErrors.le (by norm_num) binomCdf_le h

end OpenTheory.BinomialMLPDigits
