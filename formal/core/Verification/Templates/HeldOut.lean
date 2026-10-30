import Verification.Statistical.BinomialTail
import Verification.Statistical.QuantizedMLP

/-!
# Claim template `heldout-error`, v0.1

A held-out error certificate proves exactly `HeldOut.Claim ℓ h s₀ k p δ`, where:

* `ℓ` is a `{0,1}` loss;
* `h` is the hypothesis, fixed before the held-out sample `s₀` was drawn;
* `k` is the claimed error count;
* `p` is the claimed error bound;
* `δ` is the allowed failure probability.

The claim has three parts:

* `zero_one`: the loss only takes the values 0 and 1;
* `observed`: `h` makes at most `k` errors on `s₀`;
* `bound`: for **every** data distribution `D`, the event "at most `k` errors and population
  error above `p`" has probability at most `δ` over `n` IID draws.

Read together, unless `s₀` lies in an event of probability at most `δ`, the population error of
`h` is at most `p`. The IID and independence assumptions (A1, A2) are what make `s₀` a draw
from `sampleLaw D n`. They are protocol assumptions, not part of the statement.

The verifier (`verifier/core/`) writes this statement itself from the certificate's parameters,
so a certificate cannot prove a weaker statement under the template's name.
-/

open MeasureTheory StatLean.StatisticalLearning OpenTheory.BinomialTail

namespace OpenTheory.HeldOut

/-- The `heldout-error` claim. -/
structure Claim {H Z : Type*} [MeasurableSpace Z] (ℓ : H → Z → ℝ) (h : H) {n : ℕ}
    (s₀ : StatLean.StatisticalLearning.Sample Z n) (k : ℕ) (p δ : ℝ) : Prop where
  zero_one : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1
  observed : numErrors ℓ s₀ h ≤ k
  bound : ∀ (D : Measure Z) [IsProbabilityMeasure D],
    sampleLaw D n {s | numErrors ℓ s h ≤ k ∧ p < risk D ℓ h} ≤ ENNReal.ofReal δ

/-- The only route to a `Claim`: a `{0,1}` measurable loss, an observed count and a binomial tail. -/
theorem Claim.of_tail {H Z : Type*} [MeasurableSpace Z] {ℓ : H → Z → ℝ} {h : H} {n : ℕ}
    {s₀ : StatLean.StatisticalLearning.Sample Z n} {k : ℕ} {p δ : ℝ} (h01 : ∀ z, ℓ h z = 0 ∨ ℓ h z = 1)
    (hmeas : Measurable (ℓ h)) (hobs : numErrors ℓ s₀ h ≤ k) (hp : 0 ≤ p)
    (hcdf : binomCdf n k p ≤ δ) : Claim ℓ h s₀ k p δ where
  zero_one := h01
  observed := hobs
  bound D _ := by
    have := count_testSet_bound (D := D) (n := n) (measurableSet_errors hmeas) hp hcdf
    rwa [← risk_eq_measureReal h01 hmeas] at this

/-- The integer form of the tail condition that the kernel checks:
`d · tailNumerator n k a b ≤ bⁿ` gives `P(Bin(n, a/b) ≤ k) ≤ 1/d`. -/
theorem binomCdf_le_of_tailNumerator {n k a b d : ℕ} (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : d * tailNumerator n k a b ≤ b ^ n) : binomCdf n k ((a : ℝ) / b) ≤ 1 / d := by
  rw [binomCdf_div_eq _ _ hab hb, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have := (Nat.cast_le (α := ℝ)).2 h
  push_cast at this
  linarith

/-! ### Quantized MLPs (`model_type = "quantized-mlp"`) -/

theorem _root_.OpenTheory.QuantizedMLP.errorCountOfWeights_append (a : OpenTheory.QuantizedMLP.Arch)
    (ws : List ℤ) (xs ys : List OpenTheory.QuantizedMLP.Observation) :
    OpenTheory.QuantizedMLP.errorCountOfWeights a ws (xs ++ ys) =
      OpenTheory.QuantizedMLP.errorCountOfWeights a ws xs +
        OpenTheory.QuantizedMLP.errorCountOfWeights a ws ys := by
  simp [OpenTheory.QuantizedMLP.errorCountOfWeights, List.map_append, List.sum_append]

namespace QuantizedMLP
open OpenTheory.QuantizedMLP

theorem zero_one (a : Arch) (c : Code a.parameterCount 4) (z : Observation) :
    classificationLoss a c z = 0 ∨ classificationLoss a c z = 1 := by
  unfold classificationLoss errorBit errorBitOfWeights
  split <;> simp

/-- The held-out rows as a sample, in their listed order. -/
def sampleOf (rows : List Observation) : StatLean.StatisticalLearning.Sample Observation rows.length :=
  rows.get

/-- The kernel-computed error count is the `numErrors` of the statistical statement. -/
theorem numErrors_sampleOf (a : Arch) (c : Code a.parameterCount 4) (rows : List Observation) :
    numErrors (classificationLoss a) (sampleOf rows) c = errorCount a c rows := by
  have h := numErrors_eq (zero_one a c) (sampleOf rows)
  rw [sampleOf, empiricalRisk_eq_errorCount] at h
  rcases Nat.eq_zero_or_pos rows.length with h0 | hpos
  · have : rows = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    simp [numErrors, count, hits, errorCount, errorCountOfWeights]
  · have hne : (rows.length : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hne] at h
    exact_mod_cast h

/-- Builder used by generated certificates: two kernel checks give the claim. -/
theorem claim (a : Arch) (codes : List ℕ) (hlen : codes.length = a.parameterCount)
    (rows : List Observation) {k num den d : ℕ}
    (hcount : errorCountOfWeights a (weightsOfList codes) rows ≤ k)
    (hab : num ≤ den) (hden : 0 < den) (hd : 0 < d)
    (htail : d * tailNumerator rows.length k num den ≤ den ^ rows.length) :
    Claim (classificationLoss a) (codeOfList a.parameterCount codes) (sampleOf rows) k
      ((num : ℝ) / den) (1 / d) :=
  Claim.of_tail (zero_one a _) (classificationLoss_measurable a _)
    (by rw [numErrors_sampleOf, errorCount_codeOfList a codes hlen]; exact hcount)
    (by positivity) (binomCdf_le_of_tailNumerator hab hden hd htail)

end QuantizedMLP

end OpenTheory.HeldOut
