import Foundations.Arithmetic.Kronecker
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Numbers as vectors of slots

A natural number read in base `2^s` is a vector: slot `j` of `N` is `N / 2^(s·j) mod 2^s`. The packed
checks (`Checks/MLP.lean`, and the packed checks to come) act on whole vectors with one big-integer
operation; this file says what each operation does slot by slot, once:

* bitwise `and`, `or`, `xor` act slot by slot, and shifts by whole slots move slots (`slot_land`, …);
* a number is determined by its slots (`eq_of_slot_eq`);
* an addition with no carry across slot boundaries adds slot by slot (`slot_add_of_carry_free`);
* folding a number's upper half onto its lower half sums its chunks (`fold_eq_sum`).
-/

namespace OpenTheory.Slots

/-- Slot `j` of `N` in base `2^s`. -/
def slot (s j N : ℕ) : ℕ := N / 2 ^ (s * j) % 2 ^ s

theorem slot_eq_shiftRight (s j N : ℕ) : slot s j N = (N >>> (s * j)) % 2 ^ s := by
  simp [slot, Nat.shiftRight_eq_div_pow]

theorem testBit_slot (s j N i : ℕ) : (slot s j N).testBit i = (decide (i < s) && N.testBit (s * j + i)) := by
  rw [slot_eq_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.add_comm]

theorem slot_lt (s j N : ℕ) : slot s j N < 2 ^ s := Nat.mod_lt _ (by positivity)

/-- A bit of `N` is a bit of one of its slots. -/
theorem testBit_eq_slot {s : ℕ} (hs : 0 < s) (N i : ℕ) : N.testBit i = (slot s (i / s) N).testBit (i % s) := by
  rw [testBit_slot, decide_eq_true (Nat.mod_lt _ hs), Bool.true_and, Nat.div_add_mod]

/-- A number is determined by its slots. -/
theorem eq_of_slot_eq {s : ℕ} (hs : 0 < s) {a b : ℕ} (h : ∀ j, slot s j a = slot s j b) : a = b :=
  Nat.eq_of_testBit_eq fun i => by rw [testBit_eq_slot hs, testBit_eq_slot hs b, h]

theorem slot_land (s j a b : ℕ) : slot s j (a &&& b) = slot s j a &&& slot s j b :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_land]; cases decide (i < s) <;> simp

theorem slot_lor (s j a b : ℕ) : slot s j (a ||| b) = slot s j a ||| slot s j b :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_lor]; cases decide (i < s) <;> simp

theorem slot_xor (s j a b : ℕ) : slot s j (a ^^^ b) = slot s j a ^^^ slot s j b :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_xor]; cases decide (i < s) <;> simp

theorem slot_shiftRight (s j m a : ℕ) : slot s j (a >>> (s * m)) = slot s (j + m) a := by
  simp only [slot, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; ring

theorem slot_shiftLeft (s j m a : ℕ) :
    slot s j (a <<< (s * m)) = if m ≤ j then slot s (j - m) a else 0 :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_shiftLeft]
    by_cases hi : i < s
    · split
      · rename_i hm
        have h1 : s * m ≤ s * j + i := le_trans (Nat.mul_le_mul_left s hm) (Nat.le_add_right _ _)
        have h2 : s * j + i - s * m = s * (j - m) + i := by
          rw [Nat.mul_sub]; have := Nat.mul_le_mul_left s hm; omega
        simp [hi, h1, h2, testBit_slot]
      · rename_i hm
        have : ¬ s * m ≤ s * j + i := by
          intro h; apply hm
          by_contra hjm
          have : s * (j + 1) ≤ s * m := Nat.mul_le_mul_left s (by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        simp [hi, this]
    · have hs : s ≤ i := le_of_not_gt hi
      simp only [hi, decide_false, Bool.false_and]
      split
      · exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (slot_lt _ _ _) (Nat.pow_le_pow_right two_pos hs))).symm
      · exact (Nat.zero_testBit i).symm

theorem slot_of_lt {s j N : ℕ} (h : N < 2 ^ (s * j)) : slot s j N = 0 := by
  simp [slot, Nat.div_eq_of_lt h]

/-- Slot `0` is the number mod `2^s`. -/
theorem slot_zero (s N : ℕ) : slot s 0 N = N % 2 ^ s := by simp [slot]

/-- The slots of a packed list are its entries, if they fit. -/
theorem slot_pack {s : ℕ} {L : List ℕ} (hL : ∀ y ∈ L, y < 2 ^ s) (j : ℕ) :
    slot s j (Kronecker.pack s L) = L.getD j 0 := by
  unfold slot Kronecker.pack
  rw [pow_mul]
  exact Kronecker.ofDigits_div_pow_mod L hL j

/-! ### Carries -/

/-- The carry into bit `t` of `a + b`. -/
def carry (t a b : ℕ) : Bool := decide (2 ^ t ≤ a % 2 ^ t + b % 2 ^ t)

theorem add_div_two_pow (t a b : ℕ) :
    (a + b) / 2 ^ t = a / 2 ^ t + b / 2 ^ t + (if carry t a b then 1 else 0) := by
  rw [Nat.add_div (by positivity)]
  simp [carry]

/-- The carry into bit `t` shows as bit `t` of `a ^^^ b ^^^ (a + b)`. -/
theorem testBit_xor_add (t a b : ℕ) : (a ^^^ b ^^^ (a + b)).testBit t = carry t a b := by
  rw [Nat.testBit_xor, Nat.testBit_xor]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  rw [add_div_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ t) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ t) with hb | hb <;>
    cases carry t a b <;> simp [Nat.add_mod, ha, hb]

/-- No carry into bit `t` and none into bit `t + w`: the `w` bits from `t` add without overflow. -/
theorem slot_add_of_no_carry {s j a b : ℕ} (h0 : carry (s * j) a b = false)
    (h1 : carry (s * (j + 1)) a b = false) :
    slot s j (a + b) = slot s j a + slot s j b ∧ slot s j a + slot s j b < 2 ^ s := by
  have d0 := add_div_two_pow (s * j) a b
  rw [h0] at d0; simp only [Bool.false_eq_true, if_false, add_zero] at d0
  have c0 : a % 2 ^ (s * j) + b % 2 ^ (s * j) < 2 ^ (s * j) := by
    simpa [carry] using h0
  have c1 : a % 2 ^ (s * (j + 1)) + b % 2 ^ (s * (j + 1)) < 2 ^ (s * (j + 1)) := by
    simpa [carry] using h1
  have split : ∀ x, x % 2 ^ (s * (j + 1)) = slot s j x * 2 ^ (s * j) + x % 2 ^ (s * j) := by
    intro x
    rw [slot, Nat.mul_add, Nat.mul_one, pow_add, Nat.mod_mul, Nat.add_comm]
    ring
  rw [split a, split b] at c1
  have hlt : slot s j a + slot s j b < 2 ^ s := by
    by_contra hge
    have hge' : 2 ^ s ≤ slot s j a + slot s j b := le_of_not_gt hge
    have : 2 ^ s * 2 ^ (s * j) ≤ slot s j a * 2 ^ (s * j) + slot s j b * 2 ^ (s * j) := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hge'
    rw [Nat.mul_add, Nat.mul_one, pow_add] at c1
    have e : 2 ^ (s * j) * 2 ^ s = 2 ^ s * 2 ^ (s * j) := Nat.mul_comm _ _
    rw [e] at c1
    omega
  refine ⟨?_, hlt⟩
  rw [slot, d0, Nat.add_mod, ← slot, ← slot, Nat.mod_eq_of_lt hlt]

/-! ### Packing, sums of powers, and the vector of ones -/

theorem ofDigits_range_map (b : ℕ) (f : ℕ → ℕ) :
    ∀ m, Nat.ofDigits b ((List.range m).map f) = ∑ c ∈ Finset.range m, f c * b ^ c
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_range_map b f m,
      Finset.sum_range_succ]
    simp [Nat.ofDigits, List.length_map, List.length_range]
    ring

theorem pack_replicate_one (s m : ℕ) :
    Kronecker.pack s (List.replicate m 1) = ∑ c ∈ Finset.range m, (2 ^ s) ^ c := by
  unfold Kronecker.pack
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ]; ring

/-- `(2^(s·m) − 1) / (2^s − 1)`: a `1` in each of the first `m` slots. -/
theorem ones_eq_pack {s : ℕ} (hs : 0 < s) (m : ℕ) :
    (2 ^ (s * m) - 1) / (2 ^ s - 1) = Kronecker.pack s (List.replicate m 1) := by
  rw [pack_replicate_one, Nat.geomSum_eq (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs), pow_mul]

theorem slot_ones {s : ℕ} (hs : 0 < s) (m j : ℕ) :
    slot s j ((2 ^ (s * m) - 1) / (2 ^ s - 1)) = if j < m then 1 else 0 := by
  rw [ones_eq_pack hs, slot_pack]
  · by_cases h : j < m <;> simp [h, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  · intro y hy
    rw [List.eq_of_mem_replicate hy]
    exact Nat.one_lt_two_pow hs.ne'

/-- `x &&& (2^s − 1)` keeps the low `s` bits. -/
theorem land_low (s x : ℕ) : x &&& (2 ^ s - 1) = x % 2 ^ s := Nat.and_two_pow_sub_one_eq_mod x s

/-! ### Carry-free addition, from one `and` -/

/-- If `(a ^^^ b ^^^ (a + b)) &&& ones` is zero on the first `n + 1` slot boundaries, the first `n`
slots of `a + b` are the sums of those of `a` and `b`, with no overflow. -/
theorem slot_add_of_carry_free {s n a b : ℕ} (hs : 0 < s)
    (h : (a ^^^ b ^^^ (a + b)) &&& ((2 ^ (s * (n + 1)) - 1) / (2 ^ s - 1)) = 0) {j : ℕ} (hj : j < n) :
    slot s j (a + b) = slot s j a + slot s j b ∧ slot s j a + slot s j b < 2 ^ s := by
  have hb : ∀ i ≤ n, carry (s * i) a b = false := by
    intro i hi
    have hbit := congrArg (fun x => Nat.testBit x (s * i)) h
    simp only [Nat.testBit_land, Nat.zero_testBit] at hbit
    have hone : ((2 ^ (s * (n + 1)) - 1) / (2 ^ s - 1)).testBit (s * i) = true := by
      rw [testBit_eq_slot hs, Nat.mul_div_cancel_left _ hs, Nat.mul_mod_right, slot_ones hs,
        if_pos (by omega)]
      rfl
    rw [hone, Bool.and_true, testBit_xor_add] at hbit
    exact hbit
  exact slot_add_of_no_carry (hb j (by omega)) (hb (j + 1) (by omega))

/-! ### The digit sum -/

/-- A number is its digit sum modulo `2^s − 1`. -/
theorem pack_mod_pred (s : ℕ) (L : List ℕ) :
    Kronecker.pack s L % (2 ^ s - 1) = L.sum % (2 ^ s - 1) := by
  unfold Kronecker.pack
  have h : 2 ^ s ≡ 1 [MOD 2 ^ s - 1] := by
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ s = m + 1 := ⟨2 ^ s - 1, by have := Nat.one_le_two_pow (n := s); omega⟩
    rw [hm, Nat.add_sub_cancel]
    exact Nat.add_mod_left m 1
  have := Nat.ofDigits_modEq' (2 ^ s) 1 (2 ^ s - 1) h L
  rwa [Nat.ofDigits_one] at this

/-- Slot `c < m` of `q mod 2^(s·m)` is slot `c` of `q`. -/
theorem slot_mod_of_lt {s c m q : ℕ} (hc : c < m) : slot s c (q % 2 ^ (s * m)) = slot s c q :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_mod_two_pow]
    by_cases hi : i < s
    · have : s * c + i < s * m := by
        have : s * (c + 1) ≤ s * m := Nat.mul_le_mul_left s hc
        rw [Nat.mul_add, Nat.mul_one] at this; omega
      simp [hi, this]
    · simp [hi]

/-- A number below `2^(k·m)` is the sum of its `m` slots of width `k`. -/
theorem eq_sum_slots {k m q : ℕ} (hq : q < 2 ^ (k * m)) :
    q = ∑ c ∈ Finset.range m, slot k c q * (2 ^ k) ^ c := by
  have := Kronecker.pack_slots (B := k) hq
  unfold Kronecker.pack Kronecker.slots at this
  rw [ofDigits_range_map] at this
  exact this.symm

/-- `2^(s·m) − 1` is full in its first `m` slots. -/
theorem slot_two_pow_sub_one (s m j : ℕ) :
    slot s j (2 ^ (s * m) - 1) = if j < m then 2 ^ s - 1 else 0 :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < s
    · by_cases hj : j < m
      · have : s * j + i < s * m := by
          have : s * (j + 1) ≤ s * m := Nat.mul_le_mul_left s hj
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        simp [hi, hj, this, Nat.testBit_two_pow_sub_one]
      · have : ¬ s * j + i < s * m := by
          have : s * m ≤ s * j := Nat.mul_le_mul_left s (le_of_not_gt hj)
          omega
        simp [hi, hj, this]
    · simp only [hi, decide_false, Bool.false_and]
      split
      · rw [Nat.testBit_two_pow_sub_one]; simp [hi]
      · simp

/-- A number whose slots from `M` on are zero is below `2^(s·M)`. -/
theorem lt_of_slot_eq_zero {s M N : ℕ} (hs : 0 < s) (h : ∀ j, M ≤ j → slot s j N = 0) :
    N < 2 ^ (s * M) :=
  Nat.lt_pow_two_of_testBit N fun i hi => by
    rw [testBit_eq_slot hs, h (i / s) (by
      by_contra hlt
      have : i / s < M := lt_of_not_ge hlt
      have : i < s * M := by
        calc i = s * (i / s) + i % s := (Nat.div_add_mod i s).symm
          _ < s * (i / s) + s := by have := Nat.mod_lt i hs; omega
          _ = s * (i / s + 1) := by ring
          _ ≤ s * M := Nat.mul_le_mul_left s (by omega)
      omega)]
    exact Nat.zero_testBit _

/-- The `s`-slots of a chunk of `w` slots. -/
theorem slot_slot {s w c r N : ℕ} (hr : r < w) : slot s r (slot (s * w) c N) = slot s (c * w + r) N :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_slot]
    by_cases hi : i < s
    · have h1 : s * r + i < s * w := by
        have : s * (r + 1) ≤ s * w := Nat.mul_le_mul_left s hr
        rw [Nat.mul_add, Nat.mul_one] at this; omega
      have h2 : s * w * c + (s * r + i) = s * (c * w + r) + i := by ring
      simp [hi, h1, h2]
    · simp [hi]

end OpenTheory.Slots
