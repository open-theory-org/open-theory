import CertifiedDigits.PACBayesMLPDigits

-- The PAC-Bayes theorem must hold simultaneously for every posterior on an
-- arbitrary finite space, for any full-support prior and any temperature.
open MeasureTheory StatLean.StatisticalLearning OpenTheory.PACBayes

example {Z H : Type*} [MeasurableSpace Z] [Fintype H] (D : Measure Z) [IsProbabilityMeasure D]
    (ℓ : H → Z → ℝ) (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (π : H → ℝ) (hπ : ∀ h, 0 < π h) (hπ1 : ∑ h, π h = 1)
    (n : ℕ) (t δ : ℝ) (hδ : 0 < δ) :
    sampleLaw D n {s | ∃ Q, IsDist Q ∧ t * n * expect Q (empRisk ℓ s) + kl Q π +
      Real.log (1 / δ) < n * catoni t (expect Q (risk D ℓ))} ≤ ENNReal.ofReal δ :=
  catoni_pacBayes hrange hmeas hπ hπ1 n t hδ

-- The Occam bound covers any data-dependent learner, charged by its code length.
example {Z H : Type*} [MeasurableSpace Z] [Fintype H] [DecidableEq H] (D : Measure Z)
    [IsProbabilityMeasure D] (ℓ : H → Z → ℝ) (hrange : ∀ h z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (ℓ h)) (π : H → ℝ) (hπ : ∀ h, 0 < π h) (hπ1 : ∑ h, π h = 1)
    (n : ℕ) (learner : (Fin n → Z) → H) (t δ : ℝ) (hδ : 0 < δ) :
    sampleLaw D n {s | t * n * empRisk ℓ s (learner s) + Real.log (1 / π (learner s)) +
      Real.log (1 / δ) < n * catoni t (risk D ℓ (learner s))} ≤ ENNReal.ofReal δ :=
  occam_catoni hrange hmeas hπ hπ1 learner t hδ

-- Inverting the link is exact.
example (t p c : ℝ) (ht : 0 < t) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    catoni t p ≤ c ↔ p ≤ (1 - Real.exp (-c)) / (1 - Real.exp (-t)) :=
  catoni_le_iff ht hp

open OpenTheory.PACBayesMLPDigits OpenTheory.QuantizedMLP

-- The certified number refers to the saved network and the saved held-out rows.
example : errorCount arch network heldoutRows = 16 := heldout_errors
example (P : OpenTheory.Population Observation) :
    heldoutSample ∈ {s | empRisk (classificationLoss arch) s network ≤ (16 / 397 : ℝ) ∧
      (799 / 10000 : ℝ) < P.risk (classificationLoss arch network)} ↔
      (799 / 10000 : ℝ) < P.risk (classificationLoss arch network) :=
  heldoutSample_fails_iff P

#print axioms OpenTheory.PACBayes.catoni_pacBayes
#print axioms OpenTheory.PACBayes.kl_prodDist
#print axioms OpenTheory.QuantizedMLP.mlp_pacBayes
#print axioms OpenTheory.PACBayesMLPDigits.heldout_certificate
