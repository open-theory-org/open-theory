import Verification.Computation.QuantizedMLPPacked

open OpenTheory.Kronecker OpenTheory.QuantizedMLP

-- One product, one slot: 1·4 + 2·5 + 3·6 = 32 with 8-bit slots.
example : pack 8 [1, 2, 3] * pack 8 [6, 5, 4] / (2 ^ 8) ^ 2 % 2 ^ 8 = 32 := by decide
example : pack 8 [1, 2, 3] * pack 8 [4, 5, 6].reverse / (2 ^ 8) ^ ([4, 5, 6].length - 1) % 2 ^ 8 =
    (List.zipWith (· * ·) [1, 2, 3] [4, 5, 6]).sum :=
  kronecker_dot (M := 6) _ _ rfl (by decide) (by decide)

-- The mask certifies slot bounds: 0x030201 has slots 1, 2, 3 < 4.
example : (0x030201 : ℕ) &&& highMask 8 2 3 = 0 := by decide
example : ∀ y ∈ slots 8 3 0x030201, y < 2 ^ 2 :=
  slots_lt_of_land_eq_zero (by norm_num) (by decide)

-- Packed error counts are exact error counts of the decoded network.
example (a : Arch) (P : Packed) (ones : ℕ) (hP : P.Valid a ones)
    (hrest : P.rest.length = a.hidden + a.hidden * a.classes + a.classes)
    (rows : List (ℕ × ℕ)) (hrows : ∀ z ∈ rows, InputOK P.slotBits a.inputs z.1) :
    errorCount a (codeOfList _ (P.codes a)) (packedObservations P.slotBits a.inputs rows) =
      errorCountPacked a P ones rows :=
  errorCount_packed hP hrest hrows

#print axioms OpenTheory.Kronecker.kronecker_dot
#print axioms OpenTheory.QuantizedMLP.errorCount_packed
