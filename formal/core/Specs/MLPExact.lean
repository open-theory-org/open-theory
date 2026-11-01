import Checks.MLP
import Foundations.Arithmetic.Slots

/-!
# The packed MLP check is sound

`Checks.MLP.check` verifies a ReLU network's exact forward pass on packed integers
(`Checks/MLP.lean`). This file proves what an accepted check means, operation by operation, in
the language of `Foundations/Arithmetic/Slots.lean`: slot `j` of a number in base `2^s`.

Part 1: the helpers (`pow2`, `ones`, `high`), `fold` (sums its chunks) and `replicate` (copies a
slot pattern every `E` slots).
-/

open Finset OpenTheory.Slots

namespace OpenTheory.Checks.MLP

theorem pow2_eq (k : ℕ) : pow2 k = 2 ^ k := by simp [pow2, Nat.shiftLeft_eq]

theorem ones_eq (s n : ℕ) : ones s n = (2 ^ (s * n) - 1) / (2 ^ s - 1) := by
  simp only [ones, pow2_eq, Nat.mul_eq, Nat.sub_eq]; rfl

/-! ### `fold` sums its chunks -/

theorem fold_succ (k L q : ℕ) :
    fold k (L + 1) q = fold k L (q % 2 ^ (k * 2 ^ L) + q / 2 ^ (k * 2 ^ L)) := by
  show fold k L (Nat.add (Nat.land q (Nat.sub (pow2 (Nat.mul k (pow2 L))) 1))
    (Nat.shiftRight q (Nat.mul k (pow2 L)))) = _
  congr 1
  simp only [pow2_eq, Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  rw [← Nat.shiftRight_eq_div_pow]; rfl

/-- **`fold` sums the chunks.** If `q` has `2^L` chunks of `k` bits whose sum fits in `k` bits,
folding gives that sum. -/
theorem fold_eq_sum (k : ℕ) :
    ∀ (L q : ℕ), q < 2 ^ (k * 2 ^ L) → (∑ c ∈ range (2 ^ L), slot k c q) < 2 ^ k →
      fold k L q = ∑ c ∈ range (2 ^ L), slot k c q
  | 0, q, hq, _ => by
    simp only [pow_zero, Nat.mul_one] at hq
    simp [fold, slot, Nat.mod_eq_of_lt hq]
  | L + 1, q, hq, hsum => by
    rw [fold_succ]
    set w := k * 2 ^ L
    set lo := q % 2 ^ w
    set hi := q / 2 ^ w
    have hw : q < 2 ^ w * 2 ^ w := by
      rw [← pow_add]; convert hq using 2; rw [pow_succ]; ring
    have hlo : lo < 2 ^ (k * 2 ^ L) := Nat.mod_lt _ (by positivity)
    have hhi : hi < 2 ^ (k * 2 ^ L) := Nat.div_lt_of_lt_mul hw
    have slo : ∀ c < 2 ^ L, slot k c lo = slot k c q := fun c hc => slot_mod_of_lt hc
    have shi : ∀ c, slot k c hi = slot k (c + 2 ^ L) q := by
      intro c
      have := slot_shiftRight k c (2 ^ L) q
      rwa [Nat.shiftRight_eq_div_pow] at this
    have hsplit : (∑ c ∈ range (2 ^ (L + 1)), slot k c q) =
        ∑ c ∈ range (2 ^ L), (slot k c q + slot k (c + 2 ^ L) q) := by
      rw [pow_succ, Nat.mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
      congr 1; funext c; rw [Nat.add_comm (2 ^ L) c]
    rw [hsplit] at hsum ⊢
    -- the folded number is the base-`2^k` number with digits `b c`
    set b := fun c => slot k c q + slot k (c + 2 ^ L) q
    have hb : ∀ c ∈ range (2 ^ L), b c < 2 ^ k := fun c hc =>
      lt_of_le_of_lt (Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) hc) hsum
    have hq' : lo + hi = Nat.ofDigits (2 ^ k) ((List.range (2 ^ L)).map b) := by
      rw [ofDigits_range_map, eq_sum_slots hlo, eq_sum_slots hhi, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [slo c (Finset.mem_range.mp hc), shi c, ← Nat.add_mul]
    have hdig : ∀ y ∈ (List.range (2 ^ L)).map b, y < 2 ^ k := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      exact hb c (Finset.mem_range.mpr (List.mem_range.mp hc))
    have sq' : ∀ c < 2 ^ L, slot k c (lo + hi) = b c := by
      intro c hc
      rw [hq', ← Kronecker.pack, slot_pack hdig]
      simp [List.getD_eq_getElem?_getD, hc]
    have lt' : lo + hi < 2 ^ (k * 2 ^ L) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp only [Nat.zero_mul, pow_zero] at hlo hhi ⊢; omega
      · rw [hq', pow_mul]
        simpa using Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hk.ne') hdig
    have sum' : (∑ c ∈ range (2 ^ L), slot k c (lo + hi)) = ∑ c ∈ range (2 ^ L), b c :=
      Finset.sum_congr rfl fun c hc => sq' c (Finset.mem_range.mp hc)
    rw [fold_eq_sum k L (lo + hi) lt' (by rw [sum']; exact hsum), sum']

/-! ### `replicate` copies a slot pattern every `E` slots -/

theorem replicate_succ (p lg x : ℕ) :
    replicate p (lg + 1) x = replicate (p * 2) lg (x ||| x <<< p) := rfl

open Classical in
/-- If `x` holds `v` at slots `q + c·E` for `c < m` (and `0` elsewhere), `replicate` with shift
`s·E·m` holds `v` at slots `q + c·E` for `c < m · 2^lg`. -/
theorem slot_replicate {s E q v : ℕ} : ∀ (lg m x : ℕ),
    (∀ j, slot s j x = if ∃ c < m, j = q + c * E then v else 0) →
    ∀ j, slot s j (replicate (s * (E * m)) lg x) = if ∃ c < m * 2 ^ lg, j = q + c * E then v else 0
  | 0, m, x, h => by simpa [replicate] using h
  | lg + 1, m, x, h => by
    intro j
    rw [replicate_succ, show s * (E * m) * 2 = s * (E * (2 * m)) by ring]
    have key : ∀ j, slot s j (x ||| x <<< (s * (E * m))) =
        if ∃ c < 2 * m, j = q + c * E then v else 0 := by
      intro j
      rw [slot_lor, slot_shiftLeft, h]
      by_cases A : ∃ c < m, j = q + c * E
      · obtain ⟨c, hc, rfl⟩ := A
        have hA : ∃ c' < m, q + c * E = q + c' * E := ⟨c, hc, rfl⟩
        have hR : ∃ c' < 2 * m, q + c * E = q + c' * E := ⟨c, by omega, rfl⟩
        rw [if_pos hA, if_pos hR]
        split
        · rw [h]; split <;> simp
        · simp
      · rw [if_neg A]
        by_cases B : E * m ≤ j ∧ ∃ c < m, j - E * m = q + c * E
        · obtain ⟨hj, c, hc, hc'⟩ := B
          have hB : ∃ c' < m, j - E * m = q + c' * E := ⟨c, hc, hc'⟩
          have hR : ∃ c' < 2 * m, j = q + c' * E :=
            ⟨m + c, by omega, by rw [Nat.add_mul, Nat.mul_comm m E]; omega⟩
          rw [if_pos hj, h, if_pos hB, if_pos hR]
          simp
        · have : ¬ ∃ c < 2 * m, j = q + c * E := by
            rintro ⟨c, hc, rfl⟩
            by_cases hcm : c < m
            · exact A ⟨c, hcm, rfl⟩
            · apply B
              refine ⟨?_, c - m, by omega, ?_⟩
              · have : E * m ≤ c * E := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right E (by omega)
                omega
              · have : c * E = (c - m) * E + E * m := by
                  rw [Nat.mul_comm E m, ← Nat.add_mul, Nat.sub_add_cancel (by omega)]
                omega
          rw [if_neg this]
          split
          · rename_i hj
            rw [h, if_neg (fun h' => B ⟨hj, h'⟩)]; simp
          · simp
    rw [slot_replicate lg (2 * m) _ key j, show 2 * m * 2 ^ lg = m * 2 ^ (lg + 1) by ring]

/-! ### `gather` collects slots `i·E + D − 1` -/

/-- Position `c·(E − 1) + r` (with `r < E − 1`) is a row start `c'·E` (with `c' < n < E`) exactly
when `c' = c` and `r = c`. -/
theorem chunk_hit {E n c r : ℕ} (hnE : n < E) (hr : r < E - 1) :
    (∃ c' < n, c * (E - 1) + r = c' * E) ↔ (c < n ∧ r = c) := by
  have e1 : c * (E - 1) + c = c * E := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right c (by omega))]
  constructor
  · rintro ⟨c', hc', h⟩
    have hcE : c * (E - 1) = c * E - c := Nat.mul_sub_one c E
    have hle : c ≤ c * E := Nat.le_mul_of_pos_right c (by omega)
    rcases lt_trichotomy c' c with hlt | heq | hgt
    · exfalso
      -- c' ≤ c − 1 forces c ≥ E, then c' ≥ E − 1 ≥ n
      have h1 : (c' + 1) * E ≤ c * E := Nat.mul_le_mul_right E hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      have hcE' : E ≤ c := by omega
      have h2 : E * (E - 1) ≤ c * (E - 1) := Nat.mul_le_mul_right _ hcE'
      have h3 : (E - 1) * E ≤ c' * E := by rw [Nat.mul_comm (E - 1) E]; omega
      have : E - 1 ≤ c' := Nat.le_of_mul_le_mul_right h3 (by omega)
      omega
    · subst heq; exact ⟨hc', by omega⟩
    · exfalso
      have h1 : (c + 1) * E ≤ c' * E := Nat.mul_le_mul_right E hgt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
  · rintro ⟨hc, rfl⟩
    exact ⟨r, hc, e1⟩

theorem slot_small {s j g : ℕ} (hg : g < 2 ^ s) : slot s j g = if j = 0 then g else 0 := by
  split
  · subst_vars; rw [slot_zero, Nat.mod_eq_of_lt hg]
  · apply slot_of_lt
    calc g < 2 ^ s := hg
      _ ≤ 2 ^ (s * j) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right s (by omega))

theorem mul_pred_add (c E : ℕ) (hE : 0 < E) : c * (E - 1) + c = c * E := by
  rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right c hE)]

open Classical in
/-- The mask of `gather`: full slots at `D − 1 + c·E` for `c < n`. -/
theorem slot_gatherMask {s D E n lg : ℕ} (hD : 1 ≤ D) (hDE : D ≤ E) (hn : n ≤ 2 ^ lg) (j : ℕ) :
    slot s j (replicate (s * E) lg ((2 ^ s - 1) <<< (s * (D - 1))) &&& (2 ^ (s * (n * E)) - 1)) =
      if ∃ c < n, j = (D - 1) + c * E then 2 ^ s - 1 else 0 := by
  have m0 : ∀ j, slot s j ((2 ^ s - 1) <<< (s * (D - 1))) =
      if ∃ c < 1, j = (D - 1) + c * E then 2 ^ s - 1 else 0 := by
    intro j
    have one : (∃ c < 1, j = (D - 1) + c * E) ↔ j = D - 1 :=
      ⟨fun ⟨c, hc, h⟩ => by rw [Nat.lt_one_iff.mp hc] at h; simpa using h,
       fun h => ⟨0, Nat.one_pos, by simp [h]⟩⟩
    rw [slot_shiftLeft, if_congr one rfl rfl]
    have := slot_two_pow_sub_one s 1 (j - (D - 1)); rw [Nat.mul_one] at this
    by_cases hj : j = D - 1
    · subst hj
      simp only [le_refl, if_true, Nat.sub_self]
      rw [slot_zero, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos s) Nat.one_pos)]
    · rw [if_neg hj]; split
      · rw [this, if_neg (by omega)]
      · rfl
  have rep := slot_replicate (s := s) (E := E) (q := D - 1) (v := 2 ^ s - 1) lg 1 _ m0
  simp only [Nat.mul_one, Nat.one_mul] at rep
  rw [slot_land, rep, slot_two_pow_sub_one]
  by_cases h : ∃ c < n, j = (D - 1) + c * E
  · obtain ⟨c, hc, rfl⟩ := h
    have hlt : D - 1 + c * E < n * E := by
      have : (c + 1) * E ≤ n * E := Nat.mul_le_mul_right E hc
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    rw [if_pos ⟨c, lt_of_lt_of_le hc hn, rfl⟩, if_pos hlt, if_pos ⟨c, hc, rfl⟩, Nat.and_self]
  · rw [if_neg h]
    split
    · rename_i h1
      obtain ⟨c, _, rfl⟩ := h1
      have : ¬ D - 1 + c * E < n * E := by
        intro hlt
        apply h
        refine ⟨c, ?_, rfl⟩
        by_contra hcn
        have : n * E ≤ c * E := Nat.mul_le_mul_right E (by omega)
        omega
      rw [if_neg this, Nat.and_zero]
    · rw [Nat.zero_and]

open Classical in
/-- The masked and shifted number: slot `c·E` holds slot `c·E + D − 1` of `P`, for `c < n`. -/
theorem slot_gatherQ {s D E n lg : ℕ} (P : ℕ) (hD : 1 ≤ D) (hDE : D ≤ E) (hn : n ≤ 2 ^ lg) (j : ℕ) :
    slot s j ((P &&& (replicate (s * E) lg ((2 ^ s - 1) <<< (s * (D - 1))) &&&
        (2 ^ (s * (n * E)) - 1))) >>> (s * (D - 1))) =
      if ∃ c < n, j = c * E then slot s (j + (D - 1)) P else 0 := by
  rw [slot_shiftRight, slot_land, slot_gatherMask hD hDE hn]
  by_cases h : ∃ c < n, j = c * E
  · obtain ⟨c, hc, rfl⟩ := h
    rw [if_pos ⟨c, hc, by omega⟩, if_pos ⟨c, hc, rfl⟩, land_low, Nat.mod_eq_of_lt (slot_lt _ _ _)]
  · rw [if_neg (by rintro ⟨c, hc, hc'⟩; exact h ⟨c, hc, by omega⟩), if_neg h, Nat.and_zero]

open Classical in
/-- Each chunk of `E − 1` slots of that number holds one value, in its slot `c`. -/
theorem slot_gatherChunk {s E n : ℕ} {Q : ℕ} {g : ℕ → ℕ} (hs : 0 < s) (hnE : n < E)
    (hg : ∀ c, g c < 2 ^ s)
    (hQ : ∀ j, slot s j Q = if ∃ c < n, j = c * E then g (j / E) else 0) (c : ℕ) :
    slot (s * (E - 1)) c Q = if c < n then g c <<< (s * c) else 0 := by
  apply eq_of_slot_eq hs
  intro r
  by_cases hr : r < E - 1
  · rw [slot_slot hr, hQ, if_congr (chunk_hit hnE hr) rfl rfl]
    by_cases hc : c < n
    · rw [if_pos hc, slot_shiftLeft]
      by_cases hrc : r = c
      · subst hrc
        rw [if_pos ⟨hc, rfl⟩, if_pos (le_refl _), Nat.sub_self, slot_small (hg _), if_pos rfl,
          mul_pred_add r E (by omega), Nat.mul_div_cancel _ (by omega)]
      · rw [if_neg (fun h => hrc h.2)]
        split
        · rw [slot_small (hg _), if_neg (by omega)]
        · rfl
    · rw [if_neg (fun h => hc h.1), if_neg hc]
      simp [slot]
  · have hge : E - 1 ≤ r := le_of_not_gt hr
    rw [slot_of_lt (lt_of_lt_of_le (slot_lt _ _ _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left s hge)))]
    split
    · rename_i hc
      rw [slot_shiftLeft]
      split
      · rw [slot_small (hg _), if_neg (by omega)]
      · rfl
    · simp [slot]

open Classical in
/-- **What `gather` computes.** Slot `i < n` of the result is slot `i·E + D − 1` of `P`; the other
slots are zero. -/
theorem slot_gather {s D E n lg : ℕ} (P : ℕ) (hs : 0 < s) (hD : 1 ≤ D) (hDE : D ≤ E) (hnE : n < E)
    (hn : n ≤ 2 ^ lg) (i : ℕ) :
    slot s i (gather s D E n lg P) = if i < n then slot s (i * E + (D - 1)) P else 0 := by
  set Q := (P &&& (replicate (s * E) lg ((2 ^ s - 1) <<< (s * (D - 1))) &&& (2 ^ (s * (n * E)) - 1)))
    >>> (s * (D - 1)) with hQdef
  set g := fun c => slot s (c * E + (D - 1)) P
  have hg : ∀ c, g c < 2 ^ s := fun c => slot_lt _ _ _
  have hQ : ∀ j, slot s j Q = if ∃ c < n, j = c * E then g (j / E) else 0 := by
    intro j
    rw [hQdef, slot_gatherQ P hD hDE hn]
    split
    · rename_i h; obtain ⟨c, _, rfl⟩ := h
      simp only [g, Nat.mul_div_cancel _ (show 0 < E by omega)]
    · rfl
  have hgather : gather s D E n lg P = fold (s * (E - 1)) lg Q := by
    simp only [gather, pow2_eq, Nat.mul_eq, Nat.sub_eq, Nat.land_eq, hQdef]
    rfl
  -- the chunks, their sum, and the bound `fold` needs
  have hchunk := slot_gatherChunk hs hnE hg hQ
  have hsum : (∑ c ∈ range (2 ^ lg), slot (s * (E - 1)) c Q) =
      ∑ c ∈ range n, g c * (2 ^ s) ^ c := by
    rw [← Finset.sum_range_add_sum_Ico _ hn, Finset.sum_eq_zero (s := Finset.Ico n (2 ^ lg)) (fun c hc => by
      rw [hchunk, if_neg (by simp at hc; omega)]), Nat.add_zero]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hchunk, if_pos (Finset.mem_range.mp hc), Nat.shiftLeft_eq, pow_mul]
  have hdig : ∀ y ∈ (List.range n).map g, y < 2 ^ s := by
    intro y hy; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy; exact hg c
  have hbound : (∑ c ∈ range n, g c * (2 ^ s) ^ c) < (2 ^ s) ^ n := by
    rw [← ofDigits_range_map]
    simpa using Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hs.ne') hdig
  have hQlt : Q < 2 ^ (s * (E - 1) * 2 ^ lg) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have : Q = 0 := eq_of_slot_eq hs fun j => by
        rw [hQ, if_neg (by rintro ⟨c, hc, _⟩; omega)]; simp [slot]
      rw [this]; exact Nat.two_pow_pos _
    · have : Q < 2 ^ (s * ((n - 1) * E + 1)) := lt_of_slot_eq_zero hs fun j hj => by
        rw [hQ, if_neg]
        rintro ⟨c, hc, rfl⟩
        have : c * E ≤ (n - 1) * E := Nat.mul_le_mul_right E (by omega)
        omega
      refine lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) ?_)
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left s
      have e1 : (n - 1) * E = n * E - E := Nat.sub_one_mul n E
      have e2 : (E - 1) * n = n * E - n := by rw [Nat.sub_one_mul, Nat.mul_comm]
      have h1 : E ≤ n * E := Nat.le_mul_of_pos_left E hpos
      have h2 : n ≤ n * E := Nat.le_mul_of_pos_right n (by omega)
      calc (n - 1) * E + 1 ≤ (E - 1) * n := by rw [e1, e2]; omega
        _ ≤ (E - 1) * 2 ^ lg := Nat.mul_le_mul_left _ hn
  have hk : (2 ^ s) ^ n ≤ 2 ^ (s * (E - 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left s (by omega))
  rw [hgather, fold_eq_sum _ lg Q hQlt (by rw [hsum]; omega), hsum, ← ofDigits_range_map,
    ← Kronecker.pack, slot_pack hdig]
  by_cases hi : i < n
  · simp [hi, List.getD_eq_getElem?_getD, g]
  · simp [hi, List.getD_eq_getElem?_getD]

end OpenTheory.Checks.MLP
