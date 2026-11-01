import Checks.PoolRate

/-!
# The sample itself, checked by the kernel (core Lean only)

`poolCheck` counts the set bits of a vector it is given. Here the kernel also derives that vector:
it receives, for each sampled position `i`, the beacon block `bᵢ`, the pool index `jᵢ` and two
numbers `aᵢ, cᵢ` (the item's committed bytes, for example its output and its label, each read as
a number), and checks

* `jᵢ = bᵢ mod N`: the index is the one the beacon selects (`DesignSampling.deriveIndex`);
* the bit of position `i` is `aᵢ = cᵢ` (`same = 1`: the output is the counted one) or `aᵢ ≠ cᵢ`
  (`same = 0`: the output fails its label), computed by the kernel;
* the count of set bits and the tail bound, by `poolCheck` (exact tail) or `poolCheckWitness`
  (Chernoff witness).

What remains outside the kernel is cryptographic: that `bᵢ` is the beacon's expansion (A5) and that
`(aᵢ, cᵢ)` is the committed item `jᵢ` (Merkle inclusion, A12). `Specs/PoolSample.lean` proves that
an accepted check, under exactly these two facts, is the acceptance of the claim types `pool-rate`
and `rate-gap`.

Each function exists twice, as for the tree checks: with the list recursor for the kernel
(`*K`), and structurally for the compiled lane; `*_eq` proves the two equal.
-/

namespace OpenTheory.Checks

/-- One sampled position: its beacon block, the pool index, and the item's two numbers. -/
structure Drawn where
  block : Nat
  index : Nat
  a : Nat
  c : Nat

/-- The position's bit: `a = c` if `same`, `a ≠ c` otherwise. -/
def Drawn.bit (same : Bool) (x : Drawn) : Bool := cond same (Nat.beq x.a x.c) (!(Nat.beq x.a x.c))

/-- Every index is its block modulo the pool size. -/
def drawnOk (N : Nat) : List Drawn → Bool
  | [] => true
  | x :: xs => Nat.beq x.index (x.block % N) && drawnOk N xs

/-- The bits as a number: position `i` is bit `i`. -/
def drawnBits (same : Bool) : List Drawn → Nat
  | [] => 0
  | x :: xs => cond (x.bit same) 1 0 + 2 * drawnBits same xs

def drawnLen : List Drawn → Nat
  | [] => 0
  | _ :: xs => drawnLen xs + 1

/-- **`pool-sample`**: the sample derived from the blocks, its bits computed, then `poolCheck`. -/
def poolSample (N s n l k a b d : Nat) (xs : List Drawn) : Bool :=
  drawnOk N xs && Nat.beq (drawnLen xs) n && poolCheck (drawnBits (Nat.beq s 1) xs) n l k a b d

/-- **`pool-sample-witness`**: the same with a Chernoff witness `u/v`. -/
def poolSampleWitness (N s n l k a b u v d : Nat) (xs : List Drawn) : Bool :=
  drawnOk N xs && Nat.beq (drawnLen xs) n &&
    poolCheckWitness (drawnBits (Nat.beq s 1) xs) n l k a b u v d

/-! ### Kernel forms -/

noncomputable def drawnOkK (N : Nat) (xs : List Drawn) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Drawn.casesOn (motive := fun _ => Bool) x
      (fun bl ix _ _ => Nat.beq ix (Nat.mod bl N)) && ih) xs

noncomputable def drawnBitsK (same : Bool) (xs : List Drawn) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Drawn.casesOn (motive := fun _ => Nat) x
      (fun _ _ a c => Nat.add (cond (cond same (Nat.beq a c) (!(Nat.beq a c))) 1 0) (Nat.mul 2 ih))) xs

noncomputable def drawnLenK (xs : List Drawn) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) xs

noncomputable def poolSampleK (N s n l k a b d : Nat) (xs : List Drawn) : Bool :=
  drawnOkK N xs && Nat.beq (drawnLenK xs) n && poolCheck (drawnBitsK (Nat.beq s 1) xs) n l k a b d

noncomputable def poolSampleWitnessK (N s n l k a b u v d : Nat) (xs : List Drawn) : Bool :=
  drawnOkK N xs && Nat.beq (drawnLenK xs) n &&
    poolCheckWitness (drawnBitsK (Nat.beq s 1) xs) n l k a b u v d

theorem drawnOkK_eq (N : Nat) (xs : List Drawn) : drawnOkK N xs = drawnOk N xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [drawnOkK, drawnOk] at *; rw [← ih]; rfl

theorem drawnBitsK_eq (same : Bool) (xs : List Drawn) : drawnBitsK same xs = drawnBits same xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [drawnBitsK, drawnBits, Drawn.bit] at *; rw [← ih]; rfl

theorem drawnLenK_eq (xs : List Drawn) : drawnLenK xs = drawnLen xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [drawnLenK, drawnLen] at *; rw [← ih]

theorem poolSampleK_eq (N s n l k a b d : Nat) (xs : List Drawn) :
    poolSampleK N s n l k a b d xs = poolSample N s n l k a b d xs := by
  simp only [poolSampleK, poolSample, drawnOkK_eq, drawnBitsK_eq, drawnLenK_eq]

theorem poolSampleWitnessK_eq (N s n l k a b u v d : Nat) (xs : List Drawn) :
    poolSampleWitnessK N s n l k a b u v d xs = poolSampleWitness N s n l k a b u v d xs := by
  simp only [poolSampleWitnessK, poolSampleWitness, drawnOkK_eq, drawnBitsK_eq, drawnLenK_eq]

/-- The compiled lane of `pool-sample`: the request's first eight numbers, then groups of four. -/
def drawnOfList : List Nat → Option (List Drawn)
  | [] => some []
  | bl :: ix :: a :: c :: rest => (drawnOfList rest).map (⟨bl, ix, a, c⟩ :: ·)
  | _ => none

def runPoolSample : List Nat → Bool
  | N :: s :: n :: l :: k :: a :: b :: d :: rest =>
    match drawnOfList rest with
    | some xs => poolSample N s n l k a b d xs
    | none => false
  | _ => false

def runPoolSampleWitness : List Nat → Bool
  | N :: s :: n :: l :: k :: a :: b :: u :: v :: d :: rest =>
    match drawnOfList rest with
    | some xs => poolSampleWitness N s n l k a b u v d xs
    | none => false
  | _ => false

end OpenTheory.Checks

namespace OpenTheory.Checks

/-- The compiled lane runs the kernel's check on the same positions. -/
theorem runPoolSample_eq (N s n l k a b d : Nat) (rest : List Nat) :
    runPoolSample (N :: s :: n :: l :: k :: a :: b :: d :: rest) =
      match drawnOfList rest with
      | some xs => poolSampleK N s n l k a b d xs
      | none => false := by
  simp only [runPoolSample]; split <;> simp_all [poolSampleK_eq]

theorem runPoolSampleWitness_eq (N s n l k a b u v d : Nat) (rest : List Nat) :
    runPoolSampleWitness (N :: s :: n :: l :: k :: a :: b :: u :: v :: d :: rest) =
      match drawnOfList rest with
      | some xs => poolSampleWitnessK N s n l k a b u v d xs
      | none => false := by
  simp only [runPoolSampleWitness]; split <;> simp_all [poolSampleWitnessK_eq]

end OpenTheory.Checks
