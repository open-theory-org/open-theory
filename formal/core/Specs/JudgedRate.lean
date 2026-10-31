import Foundations.Probability.JudgedSampling
import Specs.PoolRate

/-!
# Claim template `judged-rate`, v0.1

A cheap grader (an AI judge, or the issuer's own labels) is committed for every pool item before
the beacon round. The round selects `n` items; the grader's verdicts on all of them, and gold
labels on the first `m`, give three `pool-rate` claims:

* `judge`: the rate of items the grader marks as failures is at most `pJ` (all `n` items);
* `missed`: the rate of failures the grader missed is at most `pA` (first `m` items, gold-graded);
* `alarms` (optional): the rate of items that are *not* false alarms is at most `pB`, so the
  false-alarm rate is at least `1 − pB` (first `m` items).

By the rectifier identity (`poolRate_rectify`) the true failure rate is at most `pJ + pA`, or
`pJ + pA + pB − 1` with `alarms`, unless the seed lies in `bad`, whose fraction is at most
`(1 + N/2^b)ⁿ δJ + (1 + N/2^b)ᵐ (δA + δB)` (`bad_frac`). This is an exact, finite-sample
version of prediction-powered inference for a failure rate: the gold labels only pay for the
grader's errors, not for the model's. With the issuer's labels as the grader it is a label audit.

References: [@angelopoulos2023prediction].
-/

open Finset OpenTheory.BinomialTail OpenTheory.DesignSampling

namespace OpenTheory.JudgedRate

variable {N m n b : ℕ}

/-- The grader passes the item, gold says it fails. -/
def missed (eT eJ : Fin N → Prop) : Fin N → Prop := fun j => eT j ∧ ¬ eJ j

/-- The grader fails the item, gold says it passes. -/
def falseAlarm (eT eJ : Fin N → Prop) : Fin N → Prop := fun j => ¬ eT j ∧ eJ j

/-- Not a false alarm. -/
def notAlarm (eT eJ : Fin N → Prop) : Fin N → Prop := fun j => ¬ falseAlarm eT eJ j

instance [DecidablePred eT] [DecidablePred eJ] : DecidablePred (missed eT eJ) :=
  fun j => inferInstanceAs (Decidable (eT j ∧ ¬ eJ j))

instance [DecidablePred eT] [DecidablePred eJ] : DecidablePred (notAlarm eT eJ) :=
  fun j => inferInstanceAs (Decidable ¬(¬ eT j ∧ eJ j))

/-- Seeds on which some `judged-rate` certificate can be wrong. -/
def bad [NeZero N] (eT eJ : Fin N → Prop) (h : m ≤ n) (δJ δA δB : ℝ) : Set (Fin n → Fin (2 ^ b)) :=
  DesignSampling.bad eJ δJ ∪
    {s | prefixSeed h s ∈ DesignSampling.bad (missed eT eJ) δA ∪ DesignSampling.bad (notAlarm eT eJ) δB}

/-- **Soundness bound.** -/
theorem bad_frac [NeZero N] (eT eJ : Fin N → Prop) (h : m ≤ n) {δJ δA δB : ℝ} (hJ : 0 ≤ δJ)
    (hA : 0 ≤ δA) (hB : 0 ≤ δB) :
    seedFrac (bad (b := b) eT eJ h δJ δA δB) ≤
      (1 + (N : ℝ) / 2 ^ b) ^ n * δJ + (1 + (N : ℝ) / 2 ^ b) ^ m * (δA + δB) := by
  unfold bad
  refine (seedFrac_union_le _ _).trans ?_
  rw [seedFrac_prefix]
  have h1 := rate_sound (n := n) (b := b) eJ hJ
  have h2 := seedFrac_union_le (n := m) (b := b) (DesignSampling.bad (missed eT eJ) δA)
    (DesignSampling.bad (notAlarm eT eJ) δB)
  have h3 := rate_sound (n := m) (b := b) (missed eT eJ) hA
  have h4 := rate_sound (n := m) (b := b) (notAlarm eT eJ) hB
  rw [mul_add]
  linarith

/-- The `judged-rate` claim without the false-alarm term. -/
structure Claim (bJ : Fin n → Bool) (bA : Fin m → Bool) (kJ kA : ℕ) (pJ pA δJ δA : ℝ) : Prop where
  judge : PoolRate.Claim bJ kJ pJ δJ
  audit : PoolRate.Claim bA kA pA δA

/-- **What a claim means.** If the bits are the grader's verdicts on the sample and the gold
verdicts on its first `m` items, for properties fixed before the seed, the true failure rate is at
most `pJ + pA`, or the seed is in `bad` (with `δB = 0`, the false-alarm part is empty). -/
theorem Claim.sound [NeZero N] (eT eJ : Fin N → Prop) [DecidablePred eT] [DecidablePred eJ]
    (h : m ≤ n) (s : Fin n → Fin (2 ^ b)) {kJ kA : ℕ} {pJ pA δJ δA : ℝ}
    (hc : Claim (fun i => decide (eJ (derive s i)))
      (fun i => decide (missed eT eJ (derive (prefixSeed h s) i))) kJ kA pJ pA δJ δA) :
    poolRate eT ≤ pJ + pA ∨ s ∈ bad eT eJ h δJ δA 0 := by
  rcases PoolRate.Claim.sound eJ s hc.judge with hJ | hJ
  · rcases PoolRate.Claim.sound (missed eT eJ) (prefixSeed h s) hc.audit with hA | hA
    · left
      have hr := poolRate_rectify eT eJ
      have hB := (poolRate_mem_Icc fun j => ¬ eT j ∧ eJ j).1
      have hm : poolRate (missed eT eJ) = poolRate (fun j => eT j ∧ ¬ eJ j) := rfl
      linarith
    · exact Or.inr (Or.inr (Or.inl hA))
  · exact Or.inr (Or.inl hJ)

/-- **With the false-alarm term.** An upper bound `pB` on the rate of items that are not false
alarms lowers the bound to `pJ + pA + pB − 1`. -/
theorem Claim.sound_alarms [NeZero N] (eT eJ : Fin N → Prop) [DecidablePred eT]
    [DecidablePred eJ] (h : m ≤ n) (s : Fin n → Fin (2 ^ b)) {kJ kA kB : ℕ} {pJ pA pB δJ δA δB : ℝ}
    (hc : Claim (fun i => decide (eJ (derive s i)))
      (fun i => decide (missed eT eJ (derive (prefixSeed h s) i))) kJ kA pJ pA δJ δA)
    (hB : PoolRate.Claim (fun i => decide (notAlarm eT eJ (derive (prefixSeed h s) i))) kB pB δB) :
    poolRate eT ≤ pJ + pA + pB - 1 ∨ s ∈ bad eT eJ h δJ δA δB := by
  rcases PoolRate.Claim.sound eJ s hc.judge with hJ | hJ
  · rcases PoolRate.Claim.sound (missed eT eJ) (prefixSeed h s) hc.audit with hA | hA
    · rcases PoolRate.Claim.sound (notAlarm eT eJ) (prefixSeed h s) hB with hN | hN
      · left
        have hr := poolRate_rectify eT eJ
        have hm : poolRate (missed eT eJ) = poolRate (fun j => eT j ∧ ¬ eJ j) := rfl
        have hn : poolRate (notAlarm eT eJ) = 1 - poolRate (fun j => ¬ eT j ∧ eJ j) :=
          poolRate_not (falseAlarm eT eJ)
        linarith
      · exact Or.inr (Or.inr (Or.inr hN))
    · exact Or.inr (Or.inr (Or.inl hA))
  · exact Or.inr (Or.inl hJ)

end OpenTheory.JudgedRate
