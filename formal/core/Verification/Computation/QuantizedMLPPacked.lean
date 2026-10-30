import Foundations.Models.QuantizedMLP
import Verification.Computation.Kronecker

/-! # Packed inference for quantized MLPs, proved equal to the list decoder

A packed network stores each first-layer row as one natural whose `B`-bit slots
are the row's codes, and keeps the remaining codes (hidden biases, output
weights, output biases) as a list. An input is one natural whose slots are its
pixels in reverse order. `scoresPacked` computes every hidden pre-activation
with one product per row (Kronecker substitution), using
`Σ (cᵢ - 2) xᵢ = Σ cᵢ xᵢ - 2 Σ xᵢ` for the signed weights.

`scoresPacked_eq` proves that it returns exactly `scoresOfWeights` of the
decoded network on the decoded input, and `errorCount_packed` transfers error
counts. The side conditions (`Packed.Valid`, `InputOK`) are a length, a
comparison and one bitwise `and` per packed number, so the kernel checks them
cheaply. The statistical theorems see only `errorCount` and apply unchanged.
-/

namespace OpenTheory.QuantizedMLP
open OpenTheory.Kronecker

/-- A network with packed first-layer rows. -/
structure Packed where
  /-- Slot width in bits. -/
  slotBits : ℕ
  /-- One natural per hidden unit; slot `i` holds the code of input weight `i`. -/
  rows1 : List ℕ
  /-- Hidden biases, output weights by class, output biases, in storage order. -/
  rest : List ℕ

/-- All codes of a packed network, in the storage order of `scoresOfWeights`. -/
def Packed.codes (a : Arch) (P : Packed) : List ℕ :=
  P.rows1.flatMap (slots P.slotBits a.inputs) ++ P.rest

/-- The input stored in `X`: slot `k` holds pixel `d - 1 - k`. -/
def image (B d X : ℕ) : List ℤ := (slots B d X).reverse.map Int.ofNat

/-- The forward pass, with one natural product per hidden unit. `ones` is the
packing of `d` ones, so `ones * X` yields the pixel sum. -/
def scoresPacked (a : Arch) (P : Packed) (ones X : ℕ) : List ℤ :=
  let B := P.slotBits
  let h := a.hidden
  let shift := 2 ^ (B * (a.inputs - 1))
  let xsum : ℤ := ((ones * X / shift % 2 ^ B : ℕ) : ℤ)
  let rest := weightsOfList P.rest
  let out := rest.drop h
  let hidden := List.zipWith (fun r b =>
      max 0 (((r * X / shift % 2 ^ B : ℕ) : ℤ) - 2 * xsum + a.hiddenBiasScale * b))
    P.rows1 (rest.take h)
  List.zipWith (fun row b => dot row hidden + a.outputBiasScale * b)
    (rows h a.classes out) ((out.drop (h * a.classes)).take a.classes)

/-- Conditions on a packed network, checked once. -/
structure Packed.Valid (a : Arch) (P : Packed) (ones : ℕ) : Prop where
  rows1_length : P.rows1.length = a.hidden
  rows1_lt : ∀ r ∈ P.rows1, r < 2 ^ (P.slotBits * a.inputs)
  rows1_mask : ∀ r ∈ P.rows1, r &&& highMask P.slotBits 2 a.inputs = 0
  ones_eq : ones = pack P.slotBits (List.replicate a.inputs 1)
  eight_le : 8 ≤ P.slotBits
  no_carry : 3 * a.inputs * 255 < 2 ^ P.slotBits

/-- Conditions on one packed input: `d` slots, each a pixel in `[0, 255]`. -/
def InputOK (B d X : ℕ) : Prop := X < 2 ^ (B * d) ∧ X &&& highMask B 8 d = 0

instance (B d X : ℕ) : Decidable (InputOK B d X) := inferInstanceAs (Decidable (_ ∧ _))

/-! ### List lemmas -/

theorem length_flatMap_slots (B d : ℕ) :
    ∀ R : List ℕ, (R.flatMap (slots B d)).length = d * R.length
  | [] => by simp
  | r :: R => by
    rw [List.flatMap_cons, List.length_append, length_slots, length_flatMap_slots B d R,
      List.length_cons, mul_add, mul_one, add_comm]

theorem Packed.length_codes (a : Arch) (P : Packed) :
    (P.codes a).length = a.inputs * P.rows1.length + P.rest.length := by
  rw [Packed.codes, List.length_append, length_flatMap_slots]

theorem weightsOfList_append (xs ys : List ℕ) :
    weightsOfList (xs ++ ys) = weightsOfList xs ++ weightsOfList ys := List.map_append ..

theorem length_weightsOfList (xs : List ℕ) : (weightsOfList xs).length = xs.length :=
  List.length_map ..

theorem rows_flatMap (B d : ℕ) (T : List ℤ) : ∀ R : List ℕ,
    rows d R.length (weightsOfList (R.flatMap (slots B d)) ++ T) =
      R.map fun r => weightsOfList (slots B d r)
  | [] => rfl
  | r :: R => by
    have hl : (weightsOfList (slots B d r)).length = d := by
      rw [length_weightsOfList, length_slots]
    rw [List.length_cons, rows, List.flatMap_cons, weightsOfList_append, List.append_assoc,
      List.take_left' hl, List.drop_left' hl, rows_flatMap B d T R, List.map_cons]

theorem zipWith_congr_mem {α β γ : Type*} {f g : α → β → γ} :
    ∀ (l : List α) (l' : List β), (∀ x ∈ l, ∀ y, f x y = g x y) →
      List.zipWith f l l' = List.zipWith g l l'
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: l, y :: l', h => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, h x (by simp),
      zipWith_congr_mem l l' fun x hx => h x (by simp [hx])]

theorem dot_shift : ∀ (s xn : List ℕ), s.length = xn.length →
    dot (s.map fun v : ℕ => (v : ℤ) - 2) (xn.map Int.ofNat) =
      (((List.zipWith (· * ·) s xn).sum : ℕ) : ℤ) - 2 * ((xn.sum : ℕ) : ℤ)
  | [], [], _ => by simp [dot]
  | v :: s, y :: xn, h => by
    have := dot_shift s xn (by simpa using h)
    simp only [dot, List.map_cons, List.zipWith_cons_cons, List.sum_cons, Int.ofNat_eq_natCast] at this ⊢
    push_cast
    rw [this]
    ring

theorem sum_zipWith_replicate_one : ∀ xn : List ℕ,
    (List.zipWith (· * ·) (List.replicate xn.length 1) xn).sum = xn.sum
  | [] => rfl
  | y :: xn => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.sum_cons,
      sum_zipWith_replicate_one xn, List.sum_cons, one_mul]

theorem sum_le_mul_length : ∀ (s : List ℕ) (m : ℕ), (∀ v ∈ s, v ≤ m) → s.sum ≤ m * s.length
  | [], _, _ => by simp
  | v :: s, m, h => by
    have := sum_le_mul_length s m fun w hw => h w (by simp [hw])
    have := h v (by simp)
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem weightsOfList_of_lt {s : List ℕ} (hs : ∀ v ∈ s, v < 4) :
    weightsOfList s = s.map fun v : ℕ => (v : ℤ) - 2 :=
  List.map_congr_left fun v hv => by rw [Nat.mod_eq_of_lt (hs v hv)]

/-! ### One hidden unit -/

/-- A packed row's pre-activation is the dot product of the decoded row and input. -/
theorem dot_packed {a : Arch} {P : Packed} {ones : ℕ} (hP : P.Valid a ones) {r X : ℕ}
    (hr : r ∈ P.rows1) (hX : InputOK P.slotBits a.inputs X) :
    dot (weightsOfList (slots P.slotBits a.inputs r)) (image P.slotBits a.inputs X) =
      ((r * X / 2 ^ (P.slotBits * (a.inputs - 1)) % 2 ^ P.slotBits : ℕ) : ℤ) -
        2 * ((ones * X / 2 ^ (P.slotBits * (a.inputs - 1)) % 2 ^ P.slotBits : ℕ) : ℤ) := by
  set B := P.slotBits
  set d := a.inputs
  set s := slots B d r
  set xn := (slots B d X).reverse
  have hs4 : ∀ v ∈ s, v < 4 := by
    simpa using slots_lt_of_land_eq_zero (by have := hP.eight_le; omega) (hP.rows1_mask r hr)
  have hxn : ∀ y ∈ xn, y ≤ 255 := fun y hy => by
    have := slots_lt_of_land_eq_zero hP.eight_le hX.2 y (List.mem_reverse.1 hy)
    omega
  have hlen : s.length = xn.length := by simp [s, xn, length_slots]
  have hxlen : xn.length = d := by simp [xn, length_slots]
  have hsum : s.sum ≤ 3 * d := by
    have := sum_le_mul_length s 3 fun v hv => by have := hs4 v hv; omega
    simpa [s, length_slots] using this
  have hpow : (2 : ℕ) ^ (B * (d - 1)) = (2 ^ B) ^ (d - 1) := pow_mul ..
  have hpr : pack B s = r := pack_slots (hP.rows1_lt r hr)
  have hpX : pack B xn.reverse = X := by rw [List.reverse_reverse]; exact pack_slots hX.1
  have hk := kronecker_dot (B := B) (M := 255) s xn hlen hxn (lt_of_le_of_lt
    (Nat.mul_le_mul_right 255 hsum) hP.no_carry)
  have hones := kronecker_dot (B := B) (M := 255) (List.replicate xn.length 1) xn (by simp) hxn
    (by simpa [hxlen, List.sum_replicate] using lt_of_le_of_lt (by omega) hP.no_carry)
  rw [hpr, hpX, hxlen] at hk
  rw [sum_zipWith_replicate_one, hpX, hxlen, ← hP.ones_eq] at hones
  rw [image, weightsOfList_of_lt hs4, dot_shift s xn hlen, hpow, hk, hones]

/-! ### The whole forward pass -/

/-- **Packed inference is exact.** On a valid packed network and a valid packed
input, `scoresPacked` equals the list decoder on the decoded network and input. -/
theorem scoresPacked_eq {a : Arch} {P : Packed} {ones : ℕ} (hP : P.Valid a ones) {X : ℕ}
    (hX : InputOK P.slotBits a.inputs X) :
    scoresOfWeights a (weightsOfList (P.codes a)) (image P.slotBits a.inputs X) =
      scoresPacked a P ones X := by
  have hflat : (weightsOfList (P.rows1.flatMap (slots P.slotBits a.inputs))).length =
      a.inputs * a.hidden := by
    rw [length_weightsOfList, length_flatMap_slots, hP.rows1_length]
  have hrows := rows_flatMap P.slotBits a.inputs (weightsOfList P.rest) P.rows1
  rw [hP.rows1_length] at hrows
  simp only [scoresOfWeights, scoresPacked, Packed.codes, weightsOfList_append,
    List.drop_left' hflat, hrows, List.zipWith_map_left]
  have hhid : List.zipWith (fun r b => max 0 (dot (weightsOfList (slots P.slotBits a.inputs r))
        (image P.slotBits a.inputs X) + a.hiddenBiasScale * b)) P.rows1
        (List.take a.hidden (weightsOfList P.rest)) =
      List.zipWith (fun r b => max 0 (((r * X / 2 ^ (P.slotBits * (a.inputs - 1)) %
        2 ^ P.slotBits : ℕ) : ℤ) - 2 * ((ones * X / 2 ^ (P.slotBits * (a.inputs - 1)) %
        2 ^ P.slotBits : ℕ) : ℤ) + a.hiddenBiasScale * b)) P.rows1
        (List.take a.hidden (weightsOfList P.rest)) :=
    zipWith_congr_mem _ _ fun r hr b => by rw [dot_packed hP hr hX]
  rw [hhid]

/-- Packed observations: each input stored as one natural. -/
def packedObservations (B d : ℕ) (rows : List (ℕ × ℕ)) : List Observation :=
  rows.map fun z => (image B d z.1, z.2)

/-- The error count computed with packed inference. -/
def errorCountPacked (a : Arch) (P : Packed) (ones : ℕ) (rows : List (ℕ × ℕ)) : ℕ :=
  (rows.map fun z => if argmaxFirst (scoresPacked a P ones z.1) = z.2 then 0 else 1).sum

/-- **Error counts transfer.** The decoded network's error count on the decoded
observations equals the packed error count. -/
theorem errorCount_packed {a : Arch} {P : Packed} {ones : ℕ} (hP : P.Valid a ones)
    (hrest : P.rest.length = a.hidden + a.hidden * a.classes + a.classes)
    {rows : List (ℕ × ℕ)} (hrows : ∀ z ∈ rows, InputOK P.slotBits a.inputs z.1) :
    errorCount a (codeOfList _ (P.codes a)) (packedObservations P.slotBits a.inputs rows) =
      errorCountPacked a P ones rows := by
  have hlen : (P.codes a).length = a.parameterCount := by
    rw [Packed.length_codes, hP.rows1_length, hrest, Arch.parameterCount]
    ring
  rw [errorCount_codeOfList a _ hlen, errorCountOfWeights, errorCountPacked, packedObservations,
    List.map_map]
  congr 1
  refine List.map_congr_left fun z hz => ?_
  simp only [Function.comp, errorBitOfWeights, scoresPacked_eq hP (hrows z hz)]

end OpenTheory.QuantizedMLP
