import Foundations.Probability.BinomialTail

/-!
# Short certificates for binomial tails

`P(Bin(n, p) ≤ k) ≤ (1 - p + p t)ⁿ / tᵏ` for every `t ∈ (0, 1]`: the Chernoff bound, with
`t = e^{-λ}`. The certifier searches for a good `t`; the kernel checks one integer inequality
instead of summing the `k + 1` terms of `tailNumerator`. With the best `t` the bound equals
`exp(-n · kl(k/n ‖ p))`, so it is looser than the exact tail, but its cost does not grow with `k`.
-/

open OpenTheory.BinomialTail

namespace OpenTheory.ChernoffWitness

/-- **Chernoff bound with a witness `t`.** -/
theorem binomCdf_le_witness {n k : ℕ} {p t : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    binomCdf n k p ≤ (1 - p + p * t) ^ n / t ^ k := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨ht0, ht1⟩ := ht
  have hq : 0 ≤ 1 - p := by linarith
  set f : ℕ → ℝ := fun i => (n.choose i : ℝ) * (p * t) ^ i * (1 - p) ^ (n - i) with hf
  have hpow : (1 - p + p * t) ^ n = ∑ i ∈ Finset.range (n + 1), f i := by
    rw [show 1 - p + p * t = p * t + (1 - p) by ring, add_pow]
    exact Finset.sum_congr rfl fun i _ => by simp only [hf]; ring
  -- Each term `i ≤ k` grows when multiplied by `t^{i-k} ≥ 1`.
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) ≤ f i / t ^ k := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [le_div_iff₀ (by positivity)]
    calc (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * t ^ k
        ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * t ^ i :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1 hik) (by positivity)
      _ = f i := by simp only [hf, mul_pow]; ring
  calc binomCdf n k p
      = ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := rfl
    _ ≤ ∑ i ∈ Finset.range (k + 1), f i / t ^ k := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (k + 1), f i) / t ^ k := by rw [Finset.sum_div]
    _ ≤ (∑ i ∈ Finset.range (n + 1), f i) / t ^ k := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rcases le_or_gt k n with hkn | hnk
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun i _ _ => by positivity
        · refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => ?_).ge
          simp only [Finset.mem_range, not_lt] at hi
          simp [hf, Nat.choose_eq_zero_of_lt (by omega : n < i)]
    _ = (1 - p + p * t) ^ n / t ^ k := by rw [hpow]

/-- The integer form the kernel checks, with `p = a/b`, `t = u/v` and `δ = 1/d`. -/
theorem binomCdf_le_of_witness {n k a b u v d : ℕ} (hab : a ≤ b) (hb : 0 < b) (hu : 0 < u)
    (huv : u ≤ v) (hd : 0 < d)
    (h : d * (b * v - a * v + a * u) ^ n * v ^ k ≤ (b * v) ^ n * u ^ k) :
    binomCdf n k ((a : ℝ) / b) ≤ 1 / d := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : (a : ℝ) / b ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hb').2 (by exact_mod_cast hab)⟩
  have ht : (u : ℝ) / v ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hv').2 (by exact_mod_cast huv)⟩
  refine (binomCdf_le_witness hp ht).trans ?_
  have hav : a * v ≤ b * v := Nat.mul_le_mul_right _ hab
  set A : ℕ := b * v - a * v + a * u with hA
  have hbase : 1 - (a : ℝ) / b + a / b * (u / v) = (A : ℝ) / (b * v) := by
    rw [hA, Nat.cast_add, Nat.cast_sub hav]
    push_cast
    field_simp
  have hcast : (d : ℝ) * A ^ n * v ^ k ≤ ((b : ℝ) * v) ^ n * u ^ k := by exact_mod_cast h
  rw [hbase, div_pow, div_pow, div_div_div_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcast]

end OpenTheory.ChernoffWitness
