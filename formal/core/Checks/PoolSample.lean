import Checks.PoolRate
import Checks.MLP

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

/-! ### Packed form

The same check on whole vectors. The request carries the `n` blocks, quotients and indices as
base-`2^S` digits of three numbers `Bk`, `Q`, `J`, and the items' two numbers as base-`2^T` digits
of `A` and `C`. The kernel checks, with a fixed number of big-integer operations:

* `Bk = N·Q + J` with no carry between slots, and every slot of `J` below `N` (one addition of
  `2^mJ − N` to every slot, then `digitsBelow`): so slot `i` of `J` is slot `i` of `Bk` mod `N`;
* the outcomes: slot `i` of `A ^^^ C` is zero exactly when `aᵢ = cᵢ`; adding `2^(T−1) − 1` to every
  slot sets its top bit exactly when it is not zero, and `differ` collects those bits;
* the count: the sum of the slots of `differ`, its remainder modulo `2^T − 1`;
* the tail bound, as before.

What it proves is in `Specs/PoolSamplePacked.lean`, about the positions the request stores.
-/

namespace OpenTheory.Checks

/-- The packed indices are the blocks modulo `N`. -/
def indicesPacked (N n S mQ mJ Bk Q J : Nat) : Bool :=
  Nat.blt 0 N && Nat.blt mJ S && MLP.digitsBelow S n mQ Q && MLP.digitsBelow S n mJ J &&
    Nat.ble (Nat.add (Nat.mul N (MLP.pow2 mQ)) (MLP.pow2 mJ)) (MLP.pow2 S) &&
    Nat.beq Bk (Nat.add (Nat.mul N Q) J) && Nat.ble N (MLP.pow2 mJ) &&
    MLP.digitsBelow S n mJ (Nat.add (Nat.mul (Nat.sub (MLP.pow2 mJ) N) (MLP.ones S n)) J)

/-- Slot `i` is `1` where `aᵢ ≠ cᵢ`, `0` where they are equal. -/
def differ (T n A C : Nat) : Nat :=
  Nat.land
    (Nat.shiftRight (Nat.add (Nat.mul (Nat.sub (MLP.pow2 (Nat.sub T 1)) 1) (MLP.ones T n)) (Nat.xor A C))
      (Nat.sub T 1))
    (MLP.ones T n)

/-- The items' numbers fit their slots with a guard bit, and the count fits a slot. -/
def itemsPacked (T n A C : Nat) : Bool :=
  Nat.ble 2 T && MLP.digitsBelow T n (Nat.sub T 1) A && MLP.digitsBelow T n (Nat.sub T 1) C &&
    Nat.blt (Nat.mul n 2) (Nat.sub (MLP.pow2 T) 1)

/-- How many positions are counted: those where `a = c` (`s = 1`) or `a ≠ c`. -/
def countPacked (s T n A C : Nat) : Nat :=
  cond (Nat.beq s 1) (Nat.sub n (Nat.mod (differ T n A C) (Nat.sub (MLP.pow2 T) 1)))
    (Nat.mod (differ T n A C) (Nat.sub (MLP.pow2 T) 1))

/-- The exact tail, `d · bⁿ P(Bin(n, a/b) ≤ k) ≤ bⁿ`. -/
def tailOk (n k a b d : Nat) : Bool :=
  Nat.ble a b && Nat.blt 0 b && Nat.blt 0 d && Nat.ble (Nat.mul d (tailFast n k a b)) (Nat.pow b n)

/-- The Chernoff witness `t = u/v`. -/
def witnessOk (n k a b u v d : Nat) : Bool :=
  Nat.ble a b && Nat.blt 0 b && Nat.blt 0 u && Nat.ble u v && Nat.blt 0 d &&
    Nat.ble (Nat.mul (Nat.mul d (Nat.pow (Nat.add (Nat.sub (Nat.mul b v) (Nat.mul a v)) (Nat.mul a u)) n))
        (Nat.pow v k))
      (Nat.mul (Nat.pow (Nat.mul b v) n) (Nat.pow u k))

/-- **`pool-sample-packed`**: `pool-sample` on packed positions, exact tail. -/
def poolSamplePacked (N s n S mQ mJ T k a b d Bk Q J A C : Nat) : Bool :=
  indicesPacked N n S mQ mJ Bk Q J && itemsPacked T n A C && Nat.ble (countPacked s T n A C) k &&
    tailOk n k a b d

/-- **`pool-sample-packed-witness`**: the same with a Chernoff witness. -/
def poolSamplePackedW (N s n S mQ mJ T k a b u v d Bk Q J A C : Nat) : Bool :=
  indicesPacked N n S mQ mJ Bk Q J && itemsPacked T n A C && Nat.ble (countPacked s T n A C) k &&
    witnessOk n k a b u v d

/-- `n` bits, one per slot of width `T`, and their count fits a slot. -/
def bitsPacked (T n X : Nat) : Bool :=
  Nat.ble 1 T && MLP.digitsBelow T n 1 X && Nat.blt (Nat.mul n 2) (Nat.sub (MLP.pow2 T) 1)

/-- **`pool-packed`**: `pool` on bits given one per slot, counted by one remainder; exact tail. -/
def poolPacked (T n k a b d X : Nat) : Bool :=
  bitsPacked T n X && Nat.ble (Nat.mod X (Nat.sub (MLP.pow2 T) 1)) k && tailOk n k a b d

/-- **`pool-packed-witness`**: the same with a Chernoff witness. -/
def poolPackedW (T n k a b u v d X : Nat) : Bool :=
  bitsPacked T n X && Nat.ble (Nat.mod X (Nat.sub (MLP.pow2 T) 1)) k && witnessOk n k a b u v d

def runPoolPacked : List Nat → Bool
  | [T, n, k, a, b, d, X] => poolPacked T n k a b d X
  | _ => false

def runPoolPackedW : List Nat → Bool
  | [T, n, k, a, b, u, v, d, X] => poolPackedW T n k a b u v d X
  | _ => false

def runPoolSamplePacked : List Nat → Bool
  | [N, s, n, S, mQ, mJ, T, k, a, b, d, Bk, Q, J, A, C] => poolSamplePacked N s n S mQ mJ T k a b d Bk Q J A C
  | _ => false

def runPoolSamplePackedW : List Nat → Bool
  | [N, s, n, S, mQ, mJ, T, k, a, b, u, v, d, Bk, Q, J, A, C] =>
    poolSamplePackedW N s n S mQ mJ T k a b u v d Bk Q J A C
  | _ => false

def showPoolSamplePacked : List Nat → String
  | [N, s, n, S, mQ, mJ, T, k, a, b, d, _, _, _, _, _] =>
    s!"pool={N} same={s} sampled={n} slots={S},{T} quotientBits={mQ} indexBits={mJ} k={k} p={a}/{b} delta=1/{d}"
  | _ => "malformed"

def showPoolSamplePackedW : List Nat → String
  | [N, s, n, S, mQ, mJ, T, k, a, b, u, v, d, _, _, _, _, _] =>
    s!"pool={N} same={s} sampled={n} slots={S},{T} quotientBits={mQ} indexBits={mJ} k={k} p={a}/{b} t={u}/{v} delta=1/{d}"
  | _ => "malformed"

end OpenTheory.Checks
