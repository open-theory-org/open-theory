/-!
# Packed exact forward pass of a ReLU MLP (core Lean only)

The check behind an exact-output certificate for a ReLU network with integer weights. It uses
only `Nat` operations that the kernel performs with GMP, so kernel evaluation runs close to the
speed of compiled code. No import beyond Lean's core.

**Encoding.** Numbers are packed in slots of `s` bits (`X = 2 ^ s`).

* A layer `[D] → [n]` with row spacing `E` (`E ≥ D`, `E > n`) stores weight `w_ik` as the
  digit `w_ik + c` (`c` is the weight offset, digits `< 2 ^ wb`) at slot `i·E + (D - 1 - k)`.
* Its bias `b_i` is the digit `b_i + 2 ^ (s - 1)` at slot `i`.
* A vector `u` of naturals is the digit `u_k` at slot `k`.
* Pre-activations `y_i` are carried as `y_i + 2 ^ (s - 1)`, so their sign is bit `s - 1`.

**One layer.** `PW * U` has the dot product `Σ_k (w_ik + c) u_k` in slot `i·E + D - 1`
(Kronecker substitution). Every slot of the product sums at most `D` products, so it is exact
when `D · (2 ^ wb - 1) · (2 ^ ab - 1) < X`. `gather` masks those `n` slots, shifts them to
`i·E = i·(E - 1) + i`, and folds the number onto itself in chunks of `E - 1` slots: slot `i`
of chunk `i` lands at slot `i`, with no overlap, in `lg` halving rounds (`n ≤ 2 ^ lg`).
Subtracting `c · Σ u` (`Σ u = U mod (X - 1)`) and adding the bias gives `y_i + 2 ^ (s - 1)`;
`noCarry` checks that no slot spilled into the next. ReLU keeps the low `s - 1` bits of the
slots whose sign bit is set.

**Kernel cost.** The kernel evaluates lazily and without sharing, and spends about 1.5 µs per
reduction step, so the check

* takes the gathered dot products `G`, the pre-activations `V` and the activations `Z` of each
  layer as witnesses and only verifies them: each operation on a large number runs once, on
  literals (`prepare` computes the witnesses, untrusted);
* moves whole vectors with a logarithmic number of big-number operations, never slot by slot;
* calls the `Nat` primitives directly (`Nat.land`, not `&&&`), writes powers of two as shifts,
  and recurses through `Nat.rec`, avoiding instance unfolding and the course-of-values encoding
  of structural recursion;
* passes layers as structures, read by projection, and recurses once per layer.

The meaning of acceptance is proved once in the library (`Specs/MLPExact.lean`).

References: Kronecker substitution [@harvey2009kronecker].
-/

namespace OpenTheory.Checks.MLP

/-- `2 ^ k`, as a shift. -/
def pow2 (k : Nat) : Nat := Nat.shiftLeft 1 k

/-- `n` slots of width `s`, each holding `1`. -/
def ones (s n : Nat) : Nat := Nat.div (Nat.sub (pow2 (Nat.mul s n)) 1) (Nat.sub (pow2 s) 1)

/-- The bits at positions `≥ b` of each of `n` slots of width `s` (for `b ≤ s`). -/
def high (s n b : Nat) : Nat := Nat.mul (ones s n) (Nat.sub (pow2 s) (pow2 b))

/-- `n` digits in base `2 ^ s`, each below `2 ^ b`. -/
def digitsBelow (s n b x : Nat) : Bool :=
  Nat.blt x (pow2 (Nat.mul s n)) && Nat.beq (Nat.land x (high s n b)) 0

/-- `r = a + b` digit by digit in base `2 ^ s`, with no carry between the `n` slots or out of
the last one: every carry would show as a set bit at a slot boundary of `a ^^^ b ^^^ r`. -/
def noCarry (s n a b r : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor (Nat.xor a b) r) (ones s (Nat.add n 1))) 0

/-- `2 ^ lg` copies of `x`, `p` bits apart. -/
def replicate (p lg x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ rec sh y => rec (Nat.mul sh 2) (Nat.lor y (Nat.shiftLeft y sh))) lg p x

/-- Fold `q`, made of `2 ^ lg` chunks of `k` bits, onto its first chunk: each round adds the
upper half onto the lower half. -/
def fold (k lg q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j rec y =>
      let w := Nat.mul k (pow2 j)
      rec (Nat.add (Nat.land y (Nat.sub (pow2 w) 1)) (Nat.shiftRight y w))) lg q

/-- Slot `i·E + D - 1` of `P` for each `i < n`, packed contiguously (`E > n`, `n ≤ 2 ^ lg`). -/
def gather (s D E n lg P : Nat) : Nat :=
  let mask := Nat.land
    (replicate (Nat.mul s E) lg (Nat.shiftLeft (Nat.sub (pow2 s) 1) (Nat.mul s (Nat.sub D 1))))
    (Nat.sub (pow2 (Nat.mul s (Nat.mul n E))) 1)
  fold (Nat.mul s (Nat.sub E 1)) lg (Nat.shiftRight (Nat.land P mask) (Nat.mul s (Nat.sub D 1)))

/-- ReLU on `n` offset pre-activations: keep the value of the slots whose sign bit is set. -/
def relu (s n v : Nat) : Nat :=
  Nat.land v
    (Nat.mul (Nat.land (Nat.shiftRight v (Nat.sub s 1)) (ones s n)) (Nat.sub (pow2 (Nat.sub s 1)) 1))

/-- One layer `[D] → [n]` on the input `U` (digits below `2 ^ ab`), given the witnesses `G`
(gathered dot products) and `V` (offset pre-activations). -/
def layerOk (s c wb ab D n E lg PW B U G V : Nat) : Bool :=
  let X := pow2 s
  let σ := Nat.mod U (Nat.sub X 1)
  let T := Nat.mul (Nat.mul c σ) (ones s n)
  let top := pow2 (Nat.mul s n)
  -- shape: rows fit their spacing, the gather has room and enough rounds
  Nat.ble 1 D && Nat.ble D E && Nat.blt n E && Nat.ble n (pow2 lg) &&
    digitsBelow s (Nat.mul n E) wb PW && digitsBelow s D ab U &&
    Nat.blt B top && Nat.blt V top &&
    -- product slots are exact, `σ` is the digit sum of `U`, `c · σ` fits a slot
    Nat.blt (Nat.mul (Nat.mul D (Nat.sub (pow2 wb) 1)) (Nat.sub (pow2 ab) 1)) X &&
    Nat.blt (Nat.mul D (Nat.sub (pow2 ab) 1)) (Nat.sub X 1) &&
    Nat.blt (Nat.mul c σ) X &&
    Nat.beq (gather s D E n lg (Nat.mul PW U)) G &&
    noCarry s n G B (Nat.add G B) && noCarry s n V T (Nat.add V T) &&
    Nat.beq (Nat.add V T) (Nat.add G B)

/-- One layer of the certificate: output width `n`, digit bound `a` of the activations it
produces (unused for the last layer), row spacing `E`, gather rounds `lg`, packed weights `PW`
and biases `B`, and the witnesses `G`, `V`, `Z`. A structure, so the kernel reads each field in
one projection step. -/
structure Layer where
  n : Nat
  a : Nat
  E : Nat
  lg : Nat
  PW : Nat
  B : Nat
  G : Nat
  V : Nat
  Z : Nat

/-- A hidden layer's activations: `Z` is the ReLU of `V`, with digits below `2 ^ a`. -/
def hiddenOk (s n a V Z : Nat) : Bool := Nat.beq (relu s n V) Z && digitsBelow s n a Z

/-- The network check. `D`, `ab`, `U`: width, digit bound and value of the current input; `Y`:
the claimed offset outputs. -/
def run (s c wb : Nat) : List Layer → Nat → Nat → Nat → Nat → Bool
  | [], _, _, _, _ => false
  | l :: rest, D, ab, U, Y =>
    layerOk s c wb ab D l.n l.E l.lg l.PW l.B U l.G l.V &&
      match rest with
      | [] => Nat.beq l.V Y
      | _ :: _ => hiddenOk s l.n l.a l.V l.Z && run s c wb rest l.n l.a l.Z Y

/-- **`mlp-exact` check.** Accepts iff the ReLU network computes the offset outputs `Y` on the
input `U` (width `D`, digits below `2 ^ a₀`). -/
def check (s c wb D a₀ U Y : Nat) (layers : List Layer) : Bool :=
  Nat.blt 1 s && run s c wb layers D a₀ U Y

/-! ## Untrusted helpers for the command line -/

/-- Group a list into chunks of `g` (the last one may be shorter). -/
def chunks (g : Nat) (xs : List Nat) : List (List Nat) :=
  if _h : g = 0 ∨ xs = [] then [] else xs.take g :: chunks g (xs.drop g)
termination_by xs.length
decreasing_by simp only [List.length_drop]; cases xs <;> simp_all; omega

/-- From the short certificate `s c wb D a₀ U Y`, then `n a E lg PW B` per layer, compute the
witnesses: the result is `s c wb D a₀ U Y`, then `n a E lg PW B G V Z` per layer. -/
def prepare : List Nat → List Nat
  | s :: c :: wb :: D :: a₀ :: U :: Y :: rest => s :: c :: wb :: D :: a₀ :: U :: Y :: go s c D U rest
  | args => args
where
  go (s c D U : Nat) : List Nat → List Nat
    | n :: a :: E :: lg :: PW :: B :: rest =>
      let G := gather s D E n lg (PW * U)
      let V := G + B - c * (U % (2 ^ s - 1)) * ones s n
      let Z := relu s n V
      n :: a :: E :: lg :: PW :: B :: G :: V :: Z :: go s c n Z rest
    | rest => rest

/-- A layer from its nine numbers. -/
def Layer.ofList : List Nat → Option Layer
  | [n, a, E, lg, PW, B, G, V, Z] => some ⟨n, a, E, lg, PW, B, G, V, Z⟩
  | _ => none

/-- The compiled lane on the flat (prepared) argument list. -/
def checkFlat : List Nat → Bool
  | s :: c :: wb :: D :: a₀ :: U :: Y :: rest =>
    match (chunks 9 rest).mapM Layer.ofList with
    | some ls => check s c wb D a₀ U Y ls
    | none => false
  | _ => false

end OpenTheory.Checks.MLP

