import Foundations.Probability.DesignSampling
import Foundations.Probability.ChernoffWitness
import Foundations.Arithmetic.FastCheck

/-!
# Claim template `pool-rate`, v0.1

A `pool-rate` certificate proves exactly `PoolRate.Claim bits k p δ`, where `bitsᵢ` is the
committed procedure's bit on the `i`-th sampled pool item:

* `observed`: at most `k` of the `n` sampled bits are set;
* `nonneg`, `tail`: `0 ≤ p` and `P(Bin(n, p) ≤ k) ≤ δ`.

What it means is `Claim.sound` together with `DesignSampling.rate_sound`: if the bits are those of
a property `e` fixed before the seed, then either the pool rate of `e` is at most `p`, or the seed
lies in a set of seeds of fraction at most `(1 + N/2^b)ⁿ · δ`.

A certificate is checked without re-proving anything: the verifier runs the `Bool` check
`FastCheck.poolCheck` (or `poolCheckWitness`) on the packed bits, compiled or in the kernel, and
`Claim.of_poolCheck` (proved once, here) says that `true` gives the claim for `bitsOf x n`.

The verifier (`verifier/core/`) also checks the bindings Lean cannot see: the commitments precede
the beacon round, the round is authentic, and each sampled item is the pool item at `seedᵢ mod N`
(Merkle inclusion). See `specs/claims/pool-rate.md`.
-/

open Finset OpenTheory.BinomialTail OpenTheory.DesignSampling OpenTheory.FastCheck

namespace OpenTheory.PoolRate

/-- The `pool-rate` claim. -/
structure Claim {n : ℕ} (bits : Fin n → Bool) (k : ℕ) (p δ : ℝ) : Prop where
  observed : (univ.filter fun i => bits i = true).card ≤ k
  nonneg : 0 ≤ p
  tail : binomCdf n k p ≤ δ

/-- Builder for small `k`: the exact tail, checked as `d · tailNumerator n k a b ≤ bⁿ`. -/
theorem Claim.of_tail {n : ℕ} {bits : Fin n → Bool} {k a b d : ℕ}
    (hobs : (univ.filter fun i => bits i = true).card ≤ k) (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : d * tailNumerator n k a b ≤ b ^ n) :
    Claim bits k ((a : ℝ) / b) (1 / d) where
  observed := hobs
  nonneg := by positivity
  tail := by
    rw [binomCdf_div_eq _ _ hab hb, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this
    linarith

/-- Builder at scale: a Chernoff witness `t = u/v`, checked as one integer inequality. -/
theorem Claim.of_witness {n : ℕ} {bits : Fin n → Bool} {k a b u v d : ℕ}
    (hobs : (univ.filter fun i => bits i = true).card ≤ k) (hab : a ≤ b) (hb : 0 < b)
    (hu : 0 < u) (huv : u ≤ v) (hd : 0 < d)
    (h : d * (b * v - a * v + a * u) ^ n * v ^ k ≤ (b * v) ^ n * u ^ k) :
    Claim bits k ((a : ℝ) / b) (1 / d) where
  observed := hobs
  nonneg := by positivity
  tail := OpenTheory.ChernoffWitness.binomCdf_le_of_witness hab hb hu huv hd h

/-- **What a claim means.** If the sampled bits are those of a property `e` fixed before the
seed, the claim is right or the seed is in `bad e δ`, a set bounded by `rate_sound`. -/
theorem Claim.sound {N n b : ℕ} [NeZero N] (e : Fin N → Prop) [DecidablePred e]
    (seed : Fin n → Fin (2 ^ b)) {k : ℕ} {p δ : ℝ}
    (hc : Claim (fun i => decide (e (derive seed i))) k p δ) :
    poolRate e ≤ p ∨ seed ∈ bad e δ := by
  refine (le_or_gt (poolRate e) p).imp_right fun hpR => ⟨k, p, ?_, hc.nonneg, hc.tail, hpR⟩
  have hobs := hc.observed
  simp only [decide_eq_true_eq] at hobs
  refine le_of_eq_of_le ?_ hobs
  unfold sampledCount
  congr 1; ext i; simp

/-! ### From the fast check to the claim -/

/-- The bits packed in `x`: bit `i` of `x`. -/
def bitsOf (x n : ℕ) : Fin n → Bool := fun i => x.testBit i

theorem popWord_eq (fuel word : ℕ) :
    popWord fuel word = ∑ i ∈ range fuel, if word.testBit i then 1 else 0 := by
  induction fuel generalizing word with
  | zero => simp [popWord]
  | succ fuel ih =>
    rw [popWord, ih, sum_range_succ']
    simp only [Nat.testBit_succ]
    rcases Nat.mod_two_eq_zero_or_one word with h | h
    · simp [h]
    · simp [h]; omega

theorem popTree_eq (l x : ℕ) :
    popTree l x = ∑ i ∈ range (64 * 2 ^ l), if x.testBit i then 1 else 0 := by
  induction l generalizing x with
  | zero => simp [popTree, popWord_eq]
  | succ l ih =>
    rw [popTree, ih, ih, show 64 * 2 ^ (l + 1) = 64 * 2 ^ l + 64 * 2 ^ l by ring, sum_range_add]
    congr 1
    · exact sum_congr rfl fun i hi => by simp [mem_range.1 hi]
    · exact sum_congr rfl fun i _ => by rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem le_levels (n : ℕ) : n ≤ 64 * 2 ^ levels n := by
  have h := Nat.lt_log2_self (n := (n + 63) / 64)
  unfold levels
  omega

/-- The set bits of `x < 2ⁿ` among its first `n` bits, counted up to any `M ≥ n`. -/
theorem card_bitsOf {x n M : ℕ} (hx : x < 2 ^ n) (hM : n ≤ M) :
    (univ.filter fun i : Fin n => bitsOf x n i = true).card =
      ∑ i ∈ range M, if x.testBit i then 1 else 0 := by
  have hfin : (univ.filter fun i : Fin n => bitsOf x n i = true).card =
      ∑ i ∈ range n, if x.testBit i then 1 else 0 := by
    rw [card_filter, ← Fin.sum_univ_eq_sum_range (fun i => if x.testBit i = true then 1 else 0) n]
    rfl
  rw [hfin]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [sum_range_add]
  have hz : ∀ i, x.testBit (n + i) = false := fun i =>
    Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [hz]

/-- After `k` Horner steps the state is `(k, C(n,k), aᵏ, Σ_{i ≤ k} C(n,i) aⁱ base^{k-i})`. -/
theorem hornerState_eq (n a base k : ℕ) :
    hornerState n a base k =
      (k, n.choose k, a ^ k, ∑ i ∈ range (k + 1), n.choose i * a ^ i * base ^ (k - i)) := by
  induction k with
  | zero => simp [hornerState]
  | succ k ih =>
    have hc : n.choose k * (n - k) / (k + 1) = n.choose (k + 1) := by
      rw [← Nat.choose_succ_right_eq]; exact Nat.mul_div_cancel _ (Nat.succ_pos k)
    rw [hornerState, ih, hornerStep, hc, sum_range_succ _ (k + 1)]
    simp only [Prod.mk.injEq, true_and, Nat.sub_self, pow_zero, mul_one]
    refine ⟨by ring, ?_⟩
    rw [sum_mul]
    refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) (by ring)
    rw [show k + 1 - i = k - i + 1 by have := mem_range.1 hi; omega, pow_succ]
    ring

/-- **The fast tail is the binomial tail numerator.** -/
theorem tailFast_eq {n k a b : ℕ} (hab : a ≤ b) : tailFast n k a b = tailNumerator n k a b := by
  rw [tailNumerator_eq, tailFast]
  split_ifs with hnk
  · rw [← sum_range_add_sum_Ico _ (show n + 1 ≤ k + 1 by omega)]
    have hz : ∑ i ∈ Ico (n + 1) (k + 1), n.choose i * a ^ i * (b - a) ^ (n - i) = 0 :=
      sum_eq_zero fun i hi => by
        rw [Nat.choose_eq_zero_of_lt (by have := (mem_Ico.1 hi).1; omega)]; simp
    rw [hz, add_zero]
    have h := add_pow a (b - a) n
    rw [Nat.add_sub_cancel' hab] at h
    simp only [Nat.cast_id] at h
    rw [h]
    exact sum_congr rfl fun i _ => by ring
  · rw [hornerState_eq, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [show n - i = (n - k) + (k - i) by have := mem_range.1 hi; omega, pow_add]
    ring

/-- **A `true` exact-tail check is a claim.** -/
theorem Claim.of_poolCheck {x n k a b d : ℕ} (h : poolCheck x n k a b d = true) :
    Claim (bitsOf x n) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hx, hk⟩, hab⟩, hb⟩, hd⟩, ht⟩ := h
  refine Claim.of_tail ?_ hab hb hd (by rwa [tailFast_eq hab] at ht)
  rw [card_bitsOf hx (le_levels n), ← popTree_eq]
  exact hk

/-- **A `true` witness check is a claim.** -/
theorem Claim.of_poolCheckWitness {x n k a b u v d : ℕ}
    (h : poolCheckWitness x n k a b u v d = true) :
    Claim (bitsOf x n) k ((a : ℝ) / b) (1 / d) := by
  simp only [poolCheckWitness, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hx, hk⟩, hab⟩, hb⟩, hu⟩, huv⟩, hd⟩, hw⟩ := h
  refine Claim.of_witness ?_ hab hb hu huv hd hw
  rw [card_bitsOf hx (le_levels n), ← popTree_eq]
  exact hk

end OpenTheory.PoolRate
