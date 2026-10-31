import Foundations.Probability.JudgedSampling

/-!
# Fixed blocks of a uniform seed are uniform

A certificate that samples several committed pools from one beacon round gives each pool its own
blocks of the expanded seed: pool `A` the first `nA` blocks, pool `B` the next `nB`. Each pool's
claim is then sound by `rate_sound` for its own blocks, because any fixed, injective choice of
blocks of a uniform seed is a uniform seed (`seedFrac_restrict`).
-/

noncomputable section
open Finset

namespace OpenTheory.DesignSampling

variable {m n b : ℕ}

/-- The blocks `ι` of a seed. -/
def restrictSeed (ι : Fin m → Fin n) (s : Fin n → Fin (2 ^ b)) : Fin m → Fin (2 ^ b) := s ∘ ι

/-- **Fixed blocks of a uniform seed are uniform.** -/
theorem seedFrac_restrict {ι : Fin m → Fin n} (hι : Function.Injective ι)
    (S : Set (Fin m → Fin (2 ^ b))) :
    seedFrac (n := n) {s | restrictSeed ι s ∈ S} = seedFrac S := by
  classical
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective ι hι
  have himg : (univ.filter fun j : Fin n => ∃ i, ι i = j).card = m := by
    have : univ.filter (fun j : Fin n => ∃ i, ι i = j) = univ.image ι := by ext j; simp
    rw [this, card_image_of_injective _ hι, card_univ, Fintype.card_fin]
  -- Each `t` has exactly `(2^b)^(n-m)` extensions.
  have hfib : ∀ t : Fin m → Fin (2 ^ b),
      (univ.filter fun s : Fin n → Fin (2 ^ b) => restrictSeed ι s = t).card =
        (2 ^ b) ^ (n - m) := by
    intro t
    have hset : (univ.filter fun s : Fin n → Fin (2 ^ b) => restrictSeed ι s = t) =
        Fintype.piFinset fun j : Fin n =>
          if h : ∃ i, ι i = j then ({t h.choose} : Finset (Fin (2 ^ b))) else univ := by
      ext s
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl j
        split_ifs with h
        · rw [mem_singleton]
          show s j = s (ι h.choose)
          rw [h.choose_spec]
        · exact mem_univ _
      · intro hs
        funext i
        have h' : ∃ i', ι i' = ι i := ⟨i, rfl⟩
        have hj := hs (ι i)
        simp only [h', ↓reduceDIte, mem_singleton] at hj
        show s (ι i) = t i
        rw [hj, hι h'.choose_spec]
    rw [hset, Fintype.card_piFinset]
    have hcard : ∀ j : Fin n, (if h : ∃ i, ι i = j then ({t h.choose} : Finset (Fin (2 ^ b)))
        else univ).card = if ∃ i, ι i = j then 1 else 2 ^ b := fun j => by
      split_ifs <;> simp
    simp only [hcard]
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    congr 1
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      fun j : Fin n => ∃ i, ι i = j
    rw [card_univ, Fintype.card_fin] at h1
    have h2 : (univ.filter fun j : Fin n => ∃ i, ι i = j).card +
        (univ.filter fun j : Fin n => ¬ ∃ i, ι i = j).card = n := by convert h1 using 3
    omega
  have hcount : (univ.filter (· ∈ {s : Fin n → Fin (2 ^ b) | restrictSeed ι s ∈ S})).card =
      (univ.filter (· ∈ S)).card * (2 ^ b) ^ (n - m) := by
    rw [card_eq_sum_card_fiberwise (f := restrictSeed ι) (t := univ.filter (· ∈ S))
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
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hpow]
  push_cast
  field_simp

end OpenTheory.DesignSampling
