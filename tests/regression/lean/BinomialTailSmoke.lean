import CertifiedDigits.BinomialMLPDigits
import LearningTheory.Generalization.OccamBinomial

-- The error count of a fixed set under an IID sample is exactly binomial.
open MeasureTheory StatLean.StatisticalLearning OpenTheory.BinomialTail

example {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D] {E : Set Z}
    (hE : MeasurableSet E) (n k : ℕ) :
    sampleLaw D n {s | count E s ≤ k} = ENNReal.ofReal (binomCdf n k (D.real E)) :=
  sampleLaw_count_le hE k

-- Uniform in the observed count: no threshold is fixed in advance.
example {Z H : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (ℓ : H → Z → ℝ) (h : H) (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1) (hmeas : Measurable (ℓ h))
    (n : ℕ) (δ : ℝ) :
    sampleLaw D n {s | binomCdf n (numErrors ℓ s h) (risk D ℓ h) ≤ δ} ≤ ENNReal.ofReal δ :=
  clopperPearson h01 hmeas δ

-- Small sanity values: P(Bin(2, 1/2) ≤ 0) = 1/4 and P(Bin(2, 1/2) ≤ 1) = 3/4.
example : binomCdf 2 0 (1 / 2) = 1 / 4 := by norm_num [binomCdf]
example : binomCdf 2 1 (1 / 2) = 3 / 4 := by norm_num [binomCdf, Finset.sum_range_succ]

open OpenTheory.BinomialMLPDigits OpenTheory.PACBayesMLPDigits OpenTheory.QuantizedMLP

-- The certified number refers to the saved network and the saved held-out rows.
example : numErrors (classificationLoss arch) heldoutSample network = 16 := heldout_numErrors
example (P : OpenTheory.Population Observation) :
    heldoutSample ∈ {s | empRisk (classificationLoss arch) s network ≤ (16 / 397 : ℝ) ∧
      (303 / 5000 : ℝ) < P.risk (classificationLoss arch network)} ↔
      (303 / 5000 : ℝ) < P.risk (classificationLoss arch network) :=
  OpenTheory.BinomialMLPDigits.heldoutSample_fails_iff P

#print axioms OpenTheory.BinomialTail.sampleLaw_count_le
#print axioms OpenTheory.BinomialTail.clopperPearson
#print axioms OpenTheory.BinomialMLPDigits.heldout_testSet_certificate
#print axioms OpenTheory.BinomialMLPDigits.heldoutSample_fails_of_risk_gt

-- Occam: any countable space, any data-dependent choice, weights summing to ≤ 1.
example {Z H : Type*} [MeasurableSpace Z] [Countable H] (D : MeasureTheory.Measure Z)
    [MeasureTheory.IsProbabilityMeasure D] (ℓ : H → Z → ℝ) (h01 : ∀ h z, ℓ h z = 0 ∨ ℓ h z = 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (w : H → ENNReal) (hw : ∑' h, w h ≤ 1) (n : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    sampleLaw D n (occamEvent ℓ D w n δ) ≤ ENNReal.ofReal δ :=
  occam_binomial h01 hmeas hw hδ

#print axioms OpenTheory.BinomialTail.occam_binomial
