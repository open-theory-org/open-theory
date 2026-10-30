import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact dot products by Kronecker substitution

Pack `c` little-endian and `x` reversed into naturals with slots of `B` bits.
Their product is the carry-free convolution of the two digit lists, so if every
convolution coefficient is below `2^B` the slot `d - 1` of the product is
exactly the dot product of `c` and `x` (`kronecker_dot`). The kernel multiplies
naturals with GMP, so one product replaces `d` list multiply-adds.

The side conditions are themselves cheap to check: a slot bound `< 2^m` on all
`d` slots of a packed number follows from one bitwise `and` with a mask
(`slot_lt_of_land_eq_zero`), and a number below `2^(B d)` is exactly the
packing of its first `d` slots (`pack_slots`). -/

namespace OpenTheory.Kronecker
open Finset

/-! ### Carry-free arithmetic on digit lists -/

/-- Slotwise sum of digit lists, without carries. -/
def addL : List ℕ → List ℕ → List ℕ
  | [], M => M
  | a :: L, [] => a :: L
  | a :: L, c :: M => (a + c) :: addL L M

/-- Product of digit lists read as polynomials, without carries. -/
def conv : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: c, x => addL (x.map (a * ·)) (0 :: conv c x)

theorem ofDigits_addL (b : ℕ) :
    ∀ L M, Nat.ofDigits b (addL L M) = Nat.ofDigits b L + Nat.ofDigits b M
  | [], M => by simp [addL, Nat.ofDigits_nil]
  | a :: L, [] => by simp [addL, Nat.ofDigits_nil]
  | a :: L, c :: M => by
    simp only [addL, Nat.ofDigits_cons, ofDigits_addL b L M]
    ring

theorem ofDigits_map_mul (b a : ℕ) :
    ∀ x, Nat.ofDigits b (x.map (a * ·)) = a * Nat.ofDigits b x
  | [] => by simp [Nat.ofDigits_nil]
  | y :: x => by
    simp only [List.map_cons, Nat.ofDigits_cons, ofDigits_map_mul b a x]
    ring

/-- The carry-free convolution evaluates to the product. -/
theorem ofDigits_conv (b : ℕ) :
    ∀ c x, Nat.ofDigits b (conv c x) = Nat.ofDigits b c * Nat.ofDigits b x
  | [], x => by simp [conv, Nat.ofDigits_nil]
  | a :: c, x => by
    rw [conv, ofDigits_addL, ofDigits_map_mul, Nat.ofDigits_cons, Nat.ofDigits_cons,
      ofDigits_conv b c x]
    ring

theorem getD_addL : ∀ (L M : List ℕ) (k : ℕ), (addL L M).getD k 0 = L.getD k 0 + M.getD k 0
  | [], M, k => by simp [addL]
  | a :: L, [], k => by simp [addL]
  | a :: L, c :: M, 0 => by simp [addL]
  | a :: L, c :: M, k + 1 => by simp only [addL, List.getD_cons_succ]; exact getD_addL L M k

theorem getD_map_mul (a : ℕ) : ∀ (x : List ℕ) (k : ℕ), (x.map (a * ·)).getD k 0 = a * x.getD k 0
  | [], k => by simp
  | y :: x, 0 => by simp
  | y :: x, k + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_mul a x k

/-- Coefficients of the convolution. -/
theorem getD_conv : ∀ (c x : List ℕ) (k : ℕ),
    (conv c x).getD k 0 = ∑ i ∈ range (k + 1), c.getD i 0 * x.getD (k - i) 0
  | [], x, k => by simp [conv]
  | a :: c, x, k => by
    rw [conv, getD_addL, getD_map_mul, sum_range_succ']
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.getD_cons_succ, getD_conv c x k, List.getD_cons_zero, Nat.sub_zero,
        Nat.add_sub_add_right]
      ring

theorem getD_le_of_forall {x : List ℕ} {M : ℕ} (hx : ∀ y ∈ x, y ≤ M) (k : ℕ) :
    x.getD k 0 ≤ M := by
  rcases lt_or_ge k x.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hx _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; exact Nat.zero_le _

theorem forall_of_getD_le {x : List ℕ} {M : ℕ} (h : ∀ k, x.getD k 0 ≤ M) : ∀ y ∈ x, y ≤ M := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  have := h k
  rwa [List.getD_eq_getElem _ _ hk] at this

/-- Every convolution coefficient is at most `(Σ c) · M` when `x ≤ M` entrywise. -/
theorem getD_conv_le {M : ℕ} : ∀ (c x : List ℕ), (∀ y ∈ x, y ≤ M) → ∀ k,
    (conv c x).getD k 0 ≤ c.sum * M
  | [], x, _, k => by simp [conv]
  | a :: c, x, hx, k => by
    rw [conv, getD_addL, getD_map_mul, List.sum_cons, add_mul]
    refine add_le_add (Nat.mul_le_mul_left a (getD_le_of_forall hx k)) ?_
    cases k with
    | zero => simp
    | succ k => simpa using getD_conv_le c x hx k

/-- Slot `k` of a list whose digits are all below `b`. -/
theorem ofDigits_div_pow_mod {b : ℕ} : ∀ (L : List ℕ), (∀ y ∈ L, y < b) → ∀ k,
    Nat.ofDigits b L / b ^ k % b = L.getD k 0
  | [], _, k => by simp [Nat.ofDigits_nil]
  | a :: L, h, 0 => by
    have ha : a < b := h a (by simp)
    simp [Nat.ofDigits_cons, Nat.mod_eq_of_lt ha]
  | a :: L, h, k + 1 => by
    have ha : a < b := h a (by simp)
    have hb : 0 < b := by omega
    rw [Nat.ofDigits_cons, pow_succ, mul_comm (b ^ k), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, zero_add,
      ofDigits_div_pow_mod L (fun y hy => h y (by simp [hy])) k, List.getD_cons_succ]

theorem sum_zipWith_eq : ∀ (c x : List ℕ), c.length = x.length →
    (List.zipWith (· * ·) c x).sum = ∑ i ∈ range x.length, c.getD i 0 * x.getD i 0
  | [], [], _ => by simp
  | a :: c, y :: x, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons, sum_range_succ',
      sum_zipWith_eq c x (by simpa using h)]
    simp [add_comm]

/-! ### Packed numbers -/

/-- Little-endian packing in slots of `B` bits. -/
def pack (B : ℕ) (L : List ℕ) : ℕ := Nat.ofDigits (2 ^ B) L

/-- **Kronecker substitution.** If `x ≤ M` entrywise and `(Σ c) · M < 2^B`, the
dot product of `c` and `x` is slot `d - 1` of `pack c * pack (reverse x)`. -/
theorem kronecker_dot {B M : ℕ} (c x : List ℕ) (hlen : c.length = x.length)
    (hx : ∀ y ∈ x, y ≤ M) (hB : c.sum * M < 2 ^ B) :
    pack B c * pack B x.reverse / (2 ^ B) ^ (x.length - 1) % 2 ^ B =
      (List.zipWith (· * ·) c x).sum := by
  have hxr : ∀ y ∈ x.reverse, y ≤ M := fun y hy => hx y (List.mem_reverse.1 hy)
  have hconv : ∀ y ∈ conv c x.reverse, y < 2 ^ B := fun y hy =>
    lt_of_le_of_lt (forall_of_getD_le (getD_conv_le c x.reverse hxr) y hy) hB
  rw [pack, pack, ← ofDigits_conv, ofDigits_div_pow_mod _ hconv, getD_conv,
    sum_zipWith_eq c x hlen]
  rcases Nat.eq_zero_or_pos x.length with h0 | hpos
  · have hc : c = [] := List.eq_nil_of_length_eq_zero (hlen.trans h0)
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero h0
    simp [hc, hx0]
  rw [Nat.sub_add_cancel hpos]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [List.getD_reverse _ (by omega), show x.length - 1 - (x.length - 1 - i) = i by omega]

/-! ### Slots, and slot bounds from one bitwise `and` -/

/-- The first `d` slots of `r`, least significant first. -/
def slots (B d r : ℕ) : List ℕ := (List.range d).map fun k => r / 2 ^ (B * k) % 2 ^ B

theorem length_slots (B d r : ℕ) : (slots B d r).length = d := by simp [slots]

theorem slots_succ (B d r : ℕ) : slots B (d + 1) r = r % 2 ^ B :: slots B d (r / 2 ^ B) := by
  simp only [slots, List.range_succ_eq_map, List.map_cons, List.map_map, mul_zero, pow_zero,
    Nat.div_one]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, Nat.div_div_eq_div_mul]
  rw [Nat.succ_eq_add_one, mul_add, mul_one, pow_add, mul_comm (2 ^ (B * k))]

/-- A number below `2^(B d)` is the packing of its first `d` slots. -/
theorem pack_slots {B : ℕ} : ∀ {d r : ℕ}, r < 2 ^ (B * d) → pack B (slots B d r) = r
  | 0, r, h => by
    have : r = 0 := by simpa using h
    simp [this, slots, pack, Nat.ofDigits_nil]
  | d + 1, r, h => by
    have hlt : r / 2 ^ B < 2 ^ (B * d) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      simpa [mul_add, add_comm] using h
    rw [slots_succ, pack, Nat.ofDigits_cons, ← pack, pack_slots hlt]
    exact Nat.mod_add_div r (2 ^ B)

/-- In each of `d` slots of `B` bits, the bits from position `m` up. -/
def highMask (B m d : ℕ) : ℕ := pack B (List.replicate d (2 ^ B - 2 ^ m))

theorem testBit_highMask {B m d i k : ℕ} (hm : m ≤ B) (hk : k < d) (hi1 : m ≤ i) (hi2 : i < B) :
    (highMask B m d).testBit (B * k + i) = true := by
  have hslot : highMask B m d / 2 ^ (B * k) % 2 ^ B = 2 ^ B - 2 ^ m := by
    rw [highMask, pack, pow_mul, ofDigits_div_pow_mod _ (fun y hy => ?_), List.getD_replicate _ hk]
    rw [List.eq_of_mem_replicate hy]
    have := Nat.one_le_two_pow (n := m)
    have := Nat.one_le_two_pow (n := B)
    omega
  have hfac : 2 ^ B - 2 ^ m = 2 ^ m * (2 ^ (B - m) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hm]
  have h := congrArg (fun n => n.testBit i) hslot
  simp only [hfac, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow] at h
  simp only [show decide (i < B) = true by simpa using hi2, Bool.true_and] at h
  rw [add_comm, h]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Slot bounds from a mask.** If `r` has no bit in the high part of any of its
first `d` slots, each of those slots is below `2^m`. -/
theorem slot_lt_of_land_eq_zero {B m d r : ℕ} (hm : m ≤ B) (h : r &&& highMask B m d = 0)
    {k : ℕ} (hk : k < d) : r / 2 ^ (B * k) % 2 ^ B < 2 ^ m := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rcases lt_or_ge i B with hiB | hiB
  · have h0 := congrArg (fun n => n.testBit (B * k + i)) h
    simp only [Nat.testBit_land, Nat.zero_testBit, testBit_highMask hm hk hi hiB,
      Bool.and_true] at h0
    rw [add_comm] at h0
    simp [h0]
  · simp [show ¬ i < B by omega]

theorem slots_lt_of_land_eq_zero {B m d r : ℕ} (hm : m ≤ B) (h : r &&& highMask B m d = 0) :
    ∀ y ∈ slots B d r, y < 2 ^ m := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact slot_lt_of_land_eq_zero hm h (List.mem_range.1 hk)

end OpenTheory.Kronecker
