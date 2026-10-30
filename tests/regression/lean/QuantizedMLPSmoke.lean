import Verification.Statistical.QuantizedMLP

-- The probability guarantee must cover sample-dependent selection of all 118
-- parameters. A fixed-model or held-out-only guarantee does not meet this contract.
open MeasureTheory StatLean.StatisticalLearning

example {Z : Type*} [MeasurableSpace Z] (P : OpenTheory.Population Z)
    (loss : (Fin 118 → Fin 4) → Z → ℝ)
    (hrange : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h, Measurable (loss h))
    (learner : (Fin 1400 → Z) → (Fin 118 → Fin 4)) :
    sampleLaw P.law 1400 {s | empRisk loss s (learner s) + 1 / 4 <
      P.risk (loss (learner s))} ≤ ENNReal.ofReal (1 / 20) := by
  exact OpenTheory.QuantizedMLP.selected_code_certificate P loss hrange hmeas learner

open OpenTheory.QuantizedMLP

private def tiny : Arch := ⟨1, 2, 2, 64, 128⟩

private def signCode : Code tiny.parameterCount 4 := codeOfList _ [3, 1, 2, 2, 3, 2, 2, 3, 2, 2]

-- Independent decoder checks: nonlinear signs, ties, and scaled output bias.
example : predict tiny signCode [64] = 0 := by decide
example : predict tiny signCode [-64] = 1 := by decide
example : predict tiny signCode [0] = 0 := by decide
example : predict tiny (codeOfList _ [3, 1, 2, 2, 3, 2, 2, 3, 2, 3]) [64] = 1 := by decide
example : predict tiny (codeOfList _ [3, 1, 2, 2, 3, 2, 2, 3, 2, 3]) [256] = 0 := by decide

#print axioms OpenTheory.QuantizedMLP.uniform_code_tail
#print axioms OpenTheory.QuantizedMLP.mlp_tail
#print axioms OpenTheory.QuantizedMLP.digits_certificate
