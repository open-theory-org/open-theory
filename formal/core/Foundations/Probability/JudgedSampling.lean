import Foundations.Probability.DesignSampling

/-!
# Two rates from one seed, and the rectifier identity

Tools for certificates that combine a cheap grader (an AI judge, or the issuer's own labels) with a
small gold-labelled audit:

* `seedFrac_prefix`: the first `m` blocks of a uniform seed are a uniform seed, so a claim read off
  a prefix of the sample is sound by `rate_sound` for `m` blocks.
* `poolRate_rectify`: for any two properties, the true rate equals the judged rate plus the
  missed rate minus the false-alarm rate. It is an identity on the pool, with no assumption.
* `poolRate_not`: complements, so a lower bound on a rate is an upper bound on its complement.
-/

noncomputable section
open Finset OpenTheory.BinomialTail
open scoped Classical

namespace OpenTheory.DesignSampling

variable {N m n b : ℕ}

/-- The first `m` blocks of a seed of `n ≥ m` blocks. -/
def prefixSeed (h : m ≤ n) (s : Fin n → Fin (2 ^ b)) : Fin m → Fin (2 ^ b) :=
  fun i => s (Fin.castLE h i)

/-- **A prefix of a uniform seed is uniform.** -/
theorem seedFrac_prefix (h : m ≤ n) (S : Set (Fin m → Fin (2 ^ b))) :
    seedFrac (n := n) (b := b) {s | prefixSeed h s ∈ S} = seedFrac S := by
  -- Each prefix `t` has exactly `(2^b)^(n-m)` extensions.
  have hfib : ∀ t : Fin m → Fin (2 ^ b),
      (univ.filter fun s : Fin n → Fin (2 ^ b) => prefixSeed h s = t).card = (2 ^ b) ^ (n - m) := by
    intro t
    have hset : (univ.filter fun s : Fin n → Fin (2 ^ b) => prefixSeed h s = t) =
        Fintype.piFinset fun j : Fin n =>
          if hj : (j : ℕ) < m then ({t ⟨j, hj⟩} : Finset (Fin (2 ^ b))) else univ := by
      ext s
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl j
        split_ifs with hj
        · simp [prefixSeed]
        · exact mem_univ _
      · intro hs
        funext i
        have := hs (Fin.castLE h i)
        simp only [Fin.val_castLE, i.isLt, dite_true, mem_singleton] at this
        simpa [prefixSeed] using this
    rw [hset, Fintype.card_piFinset]
    have hcard : ∀ j : Fin n, (if hj : (j : ℕ) < m then ({t ⟨j, hj⟩} : Finset (Fin (2 ^ b)))
        else univ).card = if (j : ℕ) < m then 1 else 2 ^ b := fun j => by
      split_ifs <;> simp
    simp only [hcard]
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    congr 1
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun j : Fin n => (j : ℕ) < m
    rw [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at h1
    omega
  have hcount : (univ.filter (· ∈ {s : Fin n → Fin (2 ^ b) | prefixSeed h s ∈ S})).card =
      (univ.filter (· ∈ S)).card * (2 ^ b) ^ (n - m) := by
    rw [card_eq_sum_card_fiberwise (f := prefixSeed h) (t := univ.filter (· ∈ S))
      fun s hs => by simpa using hs]
    rw [sum_const_nat fun t ht => ?_]
    rw [← hfib t]
    congr 1
    ext s
    simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · exact fun h' => h'.2
    · intro h'
      exact ⟨by rw [h']; simpa using ht, h'⟩
  unfold seedFrac
  rw [hcount]
  have hpow : ((2 : ℝ) ^ b) ^ n = ((2 : ℝ) ^ b) ^ m * ((2 : ℝ) ^ b) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [hpow]
  push_cast
  field_simp

theorem seedFrac_union_le (S T : Set (Fin n → Fin (2 ^ b))) :
    seedFrac (S ∪ T) ≤ seedFrac S + seedFrac T := by
  unfold seedFrac
  rw [← add_div]
  gcongr
  norm_cast
  refine (card_le_card fun x hx => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, Set.mem_union, mem_union] at hx ⊢
  exact hx

/-- **Rectifier identity.** True rate = judged rate + missed rate − false-alarm rate. -/
theorem poolRate_rectify (eT eJ : Fin N → Prop) :
    poolRate eT = poolRate eJ + poolRate (fun j => eT j ∧ ¬ eJ j) -
      poolRate (fun j => ¬ eT j ∧ eJ j) := by
  unfold poolRate
  rw [← add_div, ← sub_div]
  congr 1
  simp only [card_filter]
  push_cast
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases hT : eT j <;> by_cases hJ : eJ j <;> simp [hT, hJ]

theorem poolRate_not [NeZero N] (e : Fin N → Prop) : poolRate (fun j => ¬ e j) = 1 - poolRate e := by
  unfold poolRate
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hN]
  simp only [card_filter]
  push_cast
  rw [← sum_add_distrib]
  calc _ = ∑ _j : Fin N, (1 : ℝ) := sum_congr rfl fun j _ => by by_cases h : e j <;> simp [h]
    _ = N := by simp

end OpenTheory.DesignSampling
