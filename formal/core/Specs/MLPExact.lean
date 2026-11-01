import Checks.MLP
import Foundations.Arithmetic.Slots
import Models.Exact.MLP
import Properties.Network
import Specs.Basic

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
  set Q : ℕ := (P &&& (replicate (s * E) lg ((2 ^ s - 1) <<< (s * (D - 1))) &&& (2 ^ (s * (n * E)) - 1)))
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

/-! ## Part 2: the operations of one layer -/

theorem high_eq {s : ℕ} (hs : 0 < s) (n b : ℕ) : high s n b = Kronecker.highMask s b n := by
  show ones s n * (pow2 s - pow2 b) = _
  rw [ones_eq, ones_eq_pack hs, pow2_eq, pow2_eq, Kronecker.highMask, Kronecker.pack, Kronecker.pack,
    Nat.mul_comm, ← Kronecker.ofDigits_map_mul, List.map_replicate, Nat.mul_one]

/-- `digitsBelow` bounds the number and each of its slots. -/
theorem digitsBelow_spec {s n b x : ℕ} (hs : 0 < s) (h : digitsBelow s n b x = true) :
    x < 2 ^ (s * n) ∧ ∀ j, slot s j x < 2 ^ b := by
  simp only [digitsBelow, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, pow2_eq, Nat.mul_eq] at h
  obtain ⟨hlt, hland⟩ := h
  refine ⟨hlt, fun j => ?_⟩
  by_cases hj : j < n
  · by_cases hb : b ≤ s
    · rw [high_eq hs] at hland
      exact Kronecker.slot_lt_of_land_eq_zero hb hland hj
    · exact lt_of_lt_of_le (slot_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · rw [slot_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left s (by omega))))]
    exact Nat.two_pow_pos b

/-- `noCarry` makes an addition slot by slot. -/
theorem noCarry_spec {s n a b : ℕ} (hs : 0 < s) (h : noCarry s n a b (a + b) = true) {j : ℕ}
    (hj : j < n) : slot s j (a + b) = slot s j a + slot s j b ∧ slot s j a + slot s j b < 2 ^ s := by
  have h' : (a ^^^ b ^^^ (a + b)) &&& ((2 ^ (s * (n + 1)) - 1) / (2 ^ s - 1)) = 0 := by
    have := h; simp only [noCarry, Nat.beq_eq] at this
    rw [← ones_eq]; exact this
  exact slot_add_of_carry_free hs h' hj

theorem getD_slots (s n t j : ℕ) : (Kronecker.slots s n t).getD j 0 = if j < n then slot s j t else 0 := by
  by_cases h : j < n <;> simp [Kronecker.slots, List.getD_eq_getElem?_getD, h, slot]

/-- A number below `2^(s·n)` times a small `K` multiplies each slot, if no slot overflows. -/
theorem slot_mul_small {s n t K : ℕ} (ht : t < 2 ^ (s * n)) (hK : ∀ j, slot s j t * K < 2 ^ s) (j : ℕ) :
    slot s j (t * K) = slot s j t * K := by
  have ht' := Kronecker.pack_slots (B := s) ht
  have hdig : ∀ y ∈ (Kronecker.slots s n t).map (K * ·), y < 2 ^ s := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
    rw [Nat.mul_comm]; exact hK k
  conv_lhs => rw [← ht', Nat.mul_comm, Kronecker.pack, ← Kronecker.ofDigits_map_mul, ← Kronecker.pack,
    slot_pack hdig, Kronecker.getD_map_mul, getD_slots]
  split
  · ring
  · rename_i hj
    rw [slot_of_lt (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left s (by omega))))]; ring

/-- A value below `2^s` times the vector of ones is that value in each slot. -/
theorem slot_mul_ones {s n v : ℕ} (hs : 0 < s) (hv : v < 2 ^ s) (j : ℕ) :
    slot s j (v * ones s n) = if j < n then v else 0 := by
  rw [ones_eq, ones_eq_pack hs, Kronecker.pack, ← Kronecker.ofDigits_map_mul, List.map_replicate,
    Nat.mul_one, ← Kronecker.pack, slot_pack (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact hv)]
  by_cases h : j < n <;> simp [h, List.getD_eq_getElem?_getD, List.getElem?_replicate]

theorem ones_lt {s : ℕ} (hs : 0 < s) (n : ℕ) : ones s n < 2 ^ (s * n) := by
  rw [ones_eq, ones_eq_pack hs, Kronecker.pack, pow_mul]
  have := Nat.ofDigits_lt_base_pow_length (b := 2 ^ s) (l := List.replicate n 1)
    (Nat.one_lt_two_pow hs.ne') (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact Nat.one_lt_two_pow hs.ne')
  simpa using this

/-- The sign bit of a slot. -/
theorem testBit_sign {s d : ℕ} (hs : 0 < s) (hd : d < 2 ^ s) :
    d.testBit (s - 1) = decide (2 ^ (s - 1) ≤ d) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : (2 : ℕ) ^ s = 2 ^ (s - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hs]
  have : d / 2 ^ (s - 1) < 2 := Nat.div_lt_of_lt_mul (by rw [← h2]; exact hd)
  by_cases h : 2 ^ (s - 1) ≤ d
  · have : 1 ≤ d / 2 ^ (s - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by simpa using h)
    simp only [h, decide_true, decide_eq_true_eq]; omega
  · have : d / 2 ^ (s - 1) = 0 := Nat.div_eq_of_lt (lt_of_not_ge h)
    simp [h, this]

/-- **What `relu` computes.** Slot `j < n` keeps `v_j − 2^(s−1)` when its sign bit is set, and is
zero otherwise. -/
theorem slot_relu {s n v : ℕ} (hs : 1 < s) (j : ℕ) :
    slot s j (relu s n v) =
      if j < n ∧ 2 ^ (s - 1) ≤ slot s j v then slot s j v - 2 ^ (s - 1) else 0 := by
  have hs0 : 0 < s := by omega
  set t := Nat.land (Nat.shiftRight v (Nat.sub s 1)) (ones s n) with ht
  have st : ∀ j, slot s j t = if j < n ∧ 2 ^ (s - 1) ≤ slot s j v then 1 else 0 := by
    intro j
    have e : Nat.land (Nat.shiftRight v (Nat.sub s 1)) (ones s n) = (v >>> (s - 1)) &&& ones s n := rfl
    rw [ht, e, slot_land, ones_eq, slot_ones hs0]
    have hbit : slot s j (v >>> (s - 1)) % 2 = if 2 ^ (s - 1) ≤ slot s j v then 1 else 0 := by
      have h0 := testBit_slot s j (v >>> (s - 1)) 0
      rw [Nat.testBit_zero, Nat.testBit_shiftRight] at h0
      have h1 := testBit_slot s j v (s - 1)
      rw [testBit_sign hs0 (slot_lt _ _ _)] at h1
      simp only [hs0, decide_true, Bool.true_and, Nat.add_zero] at h0
      simp only [show s - 1 < s by omega, decide_true, Bool.true_and] at h1
      rw [show s - 1 + s * j = s * j + (s - 1) by ring, ← h1] at h0
      rcases Nat.mod_two_eq_zero_or_one (slot s j (v >>> (s - 1))) with h | h <;>
        simp only [h] at h0 ⊢ <;> split <;> simp_all
    by_cases hj : j < n
    · rw [if_pos hj, Nat.and_one_is_mod, hbit]; simp [hj]
    · rw [if_neg hj, Nat.and_zero]; simp [hj]
  have tlt : t < 2 ^ (s * n) := lt_of_le_of_lt Nat.and_le_right (ones_lt hs0 n)
  have hK : 2 ^ (s - 1) - 1 < 2 ^ s :=
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have stK : ∀ j, slot s j (t * (2 ^ (s - 1) - 1)) = slot s j t * (2 ^ (s - 1) - 1) :=
    slot_mul_small tlt fun j => by rw [st]; split <;> simp [hK]
  have e : relu s n v = v &&& (t * (2 ^ (s - 1) - 1)) := by
    simp only [relu, ht, pow2_eq, Nat.mul_eq, Nat.sub_eq]; rfl
  rw [e, slot_land, stK, st]
  split
  · rename_i h
    rw [Nat.one_mul, land_low]
    have hlt := slot_lt s j v
    have h2 : (2 : ℕ) ^ s = 2 ^ (s - 1) + 2 ^ (s - 1) := by
      rw [← Nat.two_mul, ← pow_succ', Nat.sub_add_cancel hs0]
    obtain ⟨d, hd⟩ : ∃ d, slot s j v = 2 ^ (s - 1) + d := ⟨_, (Nat.add_sub_cancel' h.2).symm⟩
    rw [hd, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
  · rw [Nat.zero_mul, Nat.and_zero]

theorem sum_range_list (f : ℕ → ℕ) : ∀ D, ((List.range D).map f).sum = ∑ i ∈ range D, f i
  | 0 => by simp
  | D + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f D,
      Finset.sum_range_succ]; simp

/-- **The product's slots** (Kronecker substitution on whole vectors): slot `p` of `PW · U` is the
convolution coefficient `Σ_i U_i · PW_(p − i)`, when every coefficient fits a slot. -/
theorem slot_product {s D m U PW au aw : ℕ} (hU : U < 2 ^ (s * D))
    (hUd : ∀ j, slot s j U ≤ au) (hPW : PW < 2 ^ (s * m)) (hPWd : ∀ j, slot s j PW ≤ aw)
    (hX : D * au * aw < 2 ^ s) (p : ℕ) :
    slot s p (PW * U) = ∑ i ∈ range (p + 1),
      (if i < D then slot s i U else 0) * (if p - i < m then slot s (p - i) PW else 0) := by
  set LU := Kronecker.slots s D U
  set LW := Kronecker.slots s m PW
  have eU : Kronecker.pack s LU = U := Kronecker.pack_slots hU
  have eW : Kronecker.pack s LW = PW := Kronecker.pack_slots hPW
  have hLW : ∀ y ∈ LW, y ≤ aw := by
    intro y hy; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy; exact hPWd k
  have hsum : LU.sum ≤ D * au := by
    have := List.sum_le_length_nsmul LU au (by intro y hy; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy; exact hUd k)
    simpa [LU, Kronecker.length_slots] using this
  have hco : ∀ k, (Kronecker.conv LU LW).getD k 0 ≤ D * au * aw := fun k =>
    le_trans (Kronecker.getD_conv_le LU LW hLW k) (Nat.mul_le_mul_right aw hsum)
  have hdig : ∀ y ∈ Kronecker.conv LU LW, y < 2 ^ s := fun y hy =>
    lt_of_le_of_lt (Kronecker.forall_of_getD_le hco y hy) hX
  have eP : PW * U = Kronecker.pack s (Kronecker.conv LU LW) := by
    rw [Kronecker.pack, Kronecker.ofDigits_conv, ← Kronecker.pack, ← Kronecker.pack, eU, eW, Nat.mul_comm]
  rw [eP, slot_pack hdig, Kronecker.getD_conv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_slots, getD_slots]

/-- **One layer.** An accepted `layerOk` means: every pre-activation slot `j < n` of `V` is
`Σ_k (w_jk − c) · u_k + B_j`, where `u_k` is slot `k` of the input `U`, `w_jk + c` is slot
`j·E + D − 1 − k` of the packed weights `PW` (the weights stored with offset `c`) and `B_j` is slot `j`
of the packed biases (the bias stored with offset `2^(s−1)`, as is `V`). -/
theorem layerOk_spec {s c wb ab D n E lg PW B U G V : ℕ} (hs : 1 < s)
    (h : layerOk s c wb ab D n E lg PW B U G V = true) :
    V < 2 ^ (s * n) ∧ ∀ j < n, (slot s j V : ℤ) =
      (∑ k ∈ range D, ((slot s (j * E + (D - 1) - k) PW : ℤ) - c) * slot s k U) + slot s j B := by
  have hs0 : 0 < s := by omega
  simp only [layerOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, pow2_eq, Nat.mul_eq,
    Nat.sub_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hDE⟩, hnE⟩, hnlg⟩, hPW⟩, hU⟩, _⟩, hV⟩, hX⟩, hσX⟩, hcσ⟩, hG⟩, nc1⟩, nc2⟩, heq⟩ := h
  refine ⟨hV, fun j hj => ?_⟩
  obtain ⟨PWlt, PWd⟩ := digitsBelow_spec hs0 hPW
  obtain ⟨Ult, Ud⟩ := digitsBelow_spec hs0 hU
  -- the digit sum of the input
  set σ := Nat.mod U (2 ^ s - 1) with hσdef
  have hσ : σ = ∑ k ∈ range D, slot s k U := by
    have hsum : (Kronecker.slots s D U).sum ≤ D * (2 ^ ab - 1) := by
      have := List.sum_le_length_nsmul (Kronecker.slots s D U) (2 ^ ab - 1) (by
        intro y hy; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
        exact Nat.le_sub_one_of_lt (Ud k))
      simpa [Kronecker.length_slots] using this
    have e : σ = (Kronecker.slots s D U).sum := by
      rw [hσdef, show Nat.mod U (2 ^ s - 1) = U % (2 ^ s - 1) from rfl]
      nth_rewrite 1 [← Kronecker.pack_slots (B := s) Ult]
      rw [pack_mod_pred, Nat.mod_eq_of_lt (by omega)]
    rw [e, Kronecker.slots, sum_range_list]; rfl
  -- the gathered dot product
  have hGj : slot s j G = ∑ k ∈ range D, slot s k U * slot s (j * E + (D - 1) - k) PW := by
    rw [← hG, slot_gather _ hs0 h1 hDE hnE hnlg, if_pos hj,
      slot_product Ult (au := 2 ^ ab - 1) (fun k => Nat.le_sub_one_of_lt (Ud k)) PWlt
        (aw := 2 ^ wb - 1) (fun k => Nat.le_sub_one_of_lt (PWd k)) (by
          calc D * (2 ^ ab - 1) * (2 ^ wb - 1) = D * (2 ^ wb - 1) * (2 ^ ab - 1) := by ring
            _ < 2 ^ s := hX)]
    have hp : j * E + (D - 1) < n * E := by
      have : (j + 1) * E ≤ n * E := Nat.mul_le_mul_right E hj
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    rw [← Finset.sum_range_add_sum_Ico _ (show D ≤ j * E + (D - 1) + 1 by omega),
      Finset.sum_eq_zero (s := Finset.Ico D _) (fun i hi => by
        simp only [Finset.mem_Ico] at hi; rw [if_neg (by omega), Nat.zero_mul]), Nat.add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_pos hi', if_pos (by omega)]
  -- the two carry-free additions and their equality
  have a1 := (noCarry_spec hs0 nc1 hj).1
  have a2 := (noCarry_spec hs0 nc2 hj).1
  have hT : slot s j (c * σ * ones s n) = c * σ := by rw [slot_mul_ones hs0 hcσ, if_pos hj]
  have hslot : slot s j V + c * σ = slot s j G + slot s j B := by
    rw [← hT, ← a2, ← a1, heq]
  rw [hGj, hσ] at hslot
  have hz : (slot s j V : ℤ) + c * ∑ k ∈ range D, (slot s k U : ℤ) =
      (∑ k ∈ range D, (slot s k U : ℤ) * slot s (j * E + (D - 1) - k) PW) + slot s j B := by
    exact_mod_cast hslot
  rw [Finset.mul_sum] at hz
  have : (∑ k ∈ range D, ((slot s (j * E + (D - 1) - k) PW : ℤ) - c) * slot s k U) =
      (∑ k ∈ range D, (slot s k U : ℤ) * slot s (j * E + (D - 1) - k) PW) -
        ∑ k ∈ range D, (c : ℤ) * slot s k U := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [this]; linarith

/-! ## Part 3: the network -/

/-- The weights a layer stores, read for input width `D`: row `j`, column `k` is `w_jk`. -/
def Layer.weights (s c D : ℕ) (l : Layer) : List (List ℤ) :=
  (List.range l.n).map fun j => (List.range D).map fun k => (slot s (j * l.E + (D - 1) - k) l.PW : ℤ) - c

/-- The biases a layer stores. -/
def Layer.bias (s : ℕ) (l : Layer) : List ℤ :=
  (List.range l.n).map fun j => (slot s j l.B : ℤ) - 2 ^ (s - 1)

/-- The network a certificate stores, layer by layer, for input width `D`. -/
def decode (s c : ℕ) : ℕ → List Layer → List Exact.LinearParams
  | _, [] => []
  | D, l :: rest => (l.weights s c D, l.bias s) :: decode s c l.n rest

/-- The integer forward pass of linear layers with ReLU between them (`Exact.reluMLP`'s run). -/
def forward : List Exact.LinearParams → List ℤ → List ℤ
  | [], x => x
  | [θ], x => Exact.linearRun θ x
  | θ :: θ' :: rest, x => forward (θ' :: rest) ((Exact.linearRun θ x).map (max · 0))

/-- The first `n` slots of `N`, as integers. -/
def vec (s n N : ℕ) : List ℤ := (List.range n).map fun j => (slot s j N : ℤ)

/-- The first `n` slots of `Y`, read with offset `2^(s−1)`: the claimed outputs. -/
def outVec (s n Y : ℕ) : List ℤ := (List.range n).map fun j => (slot s j Y : ℤ) - 2 ^ (s - 1)

/-- The width of the last layer. -/
def lastWidth : ℕ → List Layer → ℕ
  | D, [] => D
  | _, l :: rest => lastWidth l.n rest

theorem sum_range_list' {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ D, ((List.range D).map f).sum = ∑ i ∈ range D, f i
  | 0 => by simp
  | D + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_list' f D,
      Finset.sum_range_succ]; simp

theorem zipWith_range {α β γ : Type*} (f : α → β → γ) (g : ℕ → α) (h : ℕ → β) (n : ℕ) :
    List.zipWith f ((List.range n).map g) ((List.range n).map h) = (List.range n).map fun j => f (g j) (h j) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem dot_range (f g : ℕ → ℤ) (D : ℕ) :
    Exact.dot ((List.range D).map f) ((List.range D).map g) = ∑ k ∈ range D, f k * g k := by
  rw [Exact.dot, zipWith_range, sum_range_list']

/-- One accepted layer: the linear map of the stored weights sends the input to the pre-activations. -/
theorem linearRun_layer {s c wb ab D lg : ℕ} {l : Layer} {U : ℕ} (hs : 1 < s)
    (h : layerOk s c wb ab D l.n l.E lg l.PW l.B U l.G l.V = true) :
    Exact.linearRun (l.weights s c D, l.bias s) (vec s D U) = outVec s l.n l.V := by
  have ⟨_, hV⟩ := layerOk_spec hs h
  simp only [Exact.linearRun, Layer.weights, Layer.bias, vec, outVec, zipWith_range, dot_range]
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  have hj : j < l.n := by simpa using h1
  rw [hV j hj]
  ring

/-- ReLU on the pre-activations gives the next layer's input. -/
theorem relu_layer {s n V : ℕ} (hs : 1 < s) :
    (outVec s n V).map (max · 0) = vec s n (relu s n V) := by
  apply List.ext_getElem (by simp [outVec, vec])
  intro j h1 _
  simp only [outVec, vec, List.getElem_map, List.getElem_range]
  have hj : j < n := by simpa [outVec] using h1
  rw [slot_relu hs, if_congr (and_iff_right hj) rfl rfl]
  split
  · rename_i hge
    rw [Nat.cast_sub hge, max_eq_left (by push_cast; linarith [show ((2 : ℕ) ^ (s - 1) : ℤ) ≤ slot s j V from by exact_mod_cast hge])]
    push_cast; ring
  · rename_i hlt
    rw [max_eq_right (by push_cast; linarith [show (slot s j V : ℤ) < 2 ^ (s - 1) from by exact_mod_cast lt_of_not_ge hlt])]
    simp

/-- **The network.** An accepted `run` means: the integer forward pass of the stored network sends
the input slots to the claimed outputs. -/
theorem run_spec {s c wb : ℕ} (hs : 1 < s) :
    ∀ (layers : List Layer) (D ab U Y : ℕ), run s c wb layers D ab U Y = true →
      forward (decode s c D layers) (vec s D U) = outVec s (lastWidth D layers) Y
  | [], _, _, _, _, h => by simp [run] at h
  | l :: rest, D, ab, U, Y, h => by
    simp only [run, Bool.and_eq_true] at h
    obtain ⟨hl, hrest⟩ := h
    have hlin := linearRun_layer hs hl
    cases rest with
    | nil =>
      simp only [Nat.beq_eq] at hrest
      simp only [decode, forward, lastWidth, hlin, hrest]
    | cons l' rest' =>
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨hhid, hrun⟩ := hrest
      simp only [hiddenOk, Bool.and_eq_true, Nat.beq_eq] at hhid
      have ih := run_spec hs (l' :: rest') l.n l.a l.Z Y hrun
      simp only [decode, forward, lastWidth] at ih ⊢
      rw [hlin, relu_layer hs, hhid.1]
      exact ih

/-- **`mlp-exact`, soundness.** If `check` accepts, the integer forward pass of the ReLU network the
certificate stores sends its input `U` (width `D`) to its claimed outputs `Y`. -/
theorem check_spec {s c wb D a₀ U Y : ℕ} {layers : List Layer}
    (h : check s c wb D a₀ U Y layers = true) :
    forward (decode s c D layers) (vec s D U) = outVec s (lastWidth D layers) Y := by
  simp only [check, Bool.and_eq_true, Nat.blt_eq] at h
  exact run_spec h.1 layers D a₀ U Y h.2

/-! ## Part 4: the network family and the claim -/

/-- The stored layers as parameters of `Exact.reluMLP d hs o`. -/
def toParams : (d : ℕ) → (hs : List ℕ) → (o : ℕ) → List Exact.LinearParams → (Exact.reluMLP d hs o).Params
  | _, [], _, θs => θs.headD ([], [])
  | _, h :: hs, o, θs => ((θs.headD ([], []), ()), toParams h hs o θs.tail)

/-- `Exact.reluMLP`'s integer run is the forward pass of the stored layers. -/
theorem run_toParams : ∀ (d : ℕ) (hs : List ℕ) (o : ℕ) (θs : List Exact.LinearParams) (x : List ℤ),
    θs.length = hs.length + 1 → (Exact.reluMLP d hs o).run (toParams d hs o θs) x = forward θs x
  | _, [], _, [θ], x, _ => by simp [toParams, forward, Exact.reluMLP, Exact.Net.run, Exact.linear]
  | _, [], _, [], _, h => by simp at h
  | _, [], _, _ :: _ :: _, _, h => by simp at h
  | _, _ :: _, _, [], _, h => by simp at h
  | _, _ :: _, _, [_], _, h => by simp at h
  | _, h :: hs, o, θ :: θ' :: rest, x, hl => by
    simp only [toParams, Exact.reluMLP, Exact.linearReLU, Exact.Net.run, List.headD, List.tail,
      Exact.linear, Exact.relu]
    rw [run_toParams h hs o (θ' :: rest) _ (by simpa using hl)]
    rfl

theorem length_decode (s c : ℕ) : ∀ (D : ℕ) (layers : List Layer), (decode s c D layers).length = layers.length
  | _, [] => rfl
  | _, l :: rest => by simp [decode, length_decode s c l.n rest]

/-- A certificate for `mlp-exact`: the packed numbers `check` reads. -/
structure Cert where
  s : ℕ
  c : ℕ
  wb : ℕ
  a₀ : ℕ
  U : ℕ
  Y : ℕ
  layers : List Layer

/-- **`mlp-exact`** for the ReLU network `D → hs → o`: if the kernel accepts the certificate, the
network it stores sends its input to its claimed outputs, exactly (`δ = 0`). -/
theorem mlpExact_sound (D : ℕ) (hs : List ℕ) (o : ℕ) :
    Sound (MeasureTheory.Measure.dirac ())
      (fun _ (θ : Cert) => check θ.s θ.c θ.wb D θ.a₀ θ.U θ.Y θ.layers = true ∧
        θ.layers.length = hs.length + 1 ∧ lastWidth D θ.layers = o)
      (fun θ => (⟨.property ((Exact.reluMLP D hs o).OutputIs (outVec θ.s o θ.Y)),
          .region {vec θ.s D θ.U}, .all⟩ : Spec (Exact.reluMLP D hs o).Params (List ℤ)).Target
        (toParams D hs o (decode θ.s θ.c D θ.layers))) 0 := by
  rw [sound_exact_iff]
  rintro θ ⟨h, hlen, hw⟩ x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  show (Exact.reluMLP D hs o).run _ _ = _
  rw [run_toParams _ _ _ _ _ (by rw [length_decode]; exact hlen), check_spec h, hw]

end OpenTheory.Checks.MLP
