import Checks.Tree
import Checks.MLP

/-!
# Linear and logistic-regression models: checks (core Lean only)

A linear model scores `bias + Σ_f w_f · x_f` and approves when `τ ≤ score`; a logistic regression
is one, its probability threshold `p` being the score threshold `log (p / (1 − p))`. Weights and
bounds are integers (the producer scales the model exactly, as for trees). Boxes are those of the
tree checks (`Checks.Tree.Box`): optional closed bounds per feature.

* `minScore ws B` is the least `Σ w_f x_f` over the box: each term at the corner its sign picks
  (`lo` if `w ≥ 0`, `hi` otherwise), `none` when a feature with a non-zero weight is unbounded
  on that side; `maxScore` the greatest.
* `robust` accepts `c = true` when `τ ≤ bias + minScore`, `c = false` when `bias + maxScore < τ`.
* `monotone` accepts when the weight of feature `j` has the sign the claim asks for.

Both are exact, not only sound: the minimum of a linear function over a box is at a corner. The
kernel spends one step per feature, so the check takes a fraction of a millisecond.
-/

namespace OpenTheory.Checks.Linear

open OpenTheory.Checks.Tree (Bound Box intLe intLt)

/-- The least value of `w · x` for `x` within the bound, if bounded. -/
def termMin (w : Int) (b : Bound) : Option Int :=
  if intLe 0 w then (if intLe w 0 then some 0 else b.lo.map (w * ·)) else b.hi.map (w * ·)

/-- The greatest value of `w · x` for `x` within the bound, if bounded. -/
def termMax (w : Int) (b : Bound) : Option Int :=
  if intLe 0 w then (if intLe w 0 then some 0 else b.hi.map (w * ·)) else b.lo.map (w * ·)

/-- `Σ_f min (w_f · x_f)` over the box, feature `f` of the list against bound `f` of the box. -/
def minScore : List Int → Box → Option Int
  | [], _ => some 0
  | w :: ws, [] => (termMin w {}).bind fun t => (minScore ws []).map (t + ·)
  | w :: ws, b :: B => (termMin w b).bind fun t => (minScore ws B).map (t + ·)

def maxScore : List Int → Box → Option Int
  | [], _ => some 0
  | w :: ws, [] => (termMax w {}).bind fun t => (maxScore ws []).map (t + ·)
  | w :: ws, b :: B => (termMax w b).bind fun t => (maxScore ws B).map (t + ·)

/-- **Robustness check.** Approve (`c = true`) on the whole box, or decline on it. -/
def robust (bias τ : Int) (ws : List Int) (B : Box) (c : Bool) : Bool :=
  if c then (match minScore ws B with | some s => intLe τ (bias + s) | none => false)
  else (match maxScore ws B with | some s => intLt (bias + s) τ | none => false)

/-- **Monotonicity check.** The weight of feature `j` (zero past the list) has the asked sign. -/
def monotone (ws : List Int) (j : Nat) (up : Bool) : Bool :=
  match ws[j]? with
  | some w => if up then intLe 0 w else intLe w 0
  | none => true

/-! ## Requests (as for the tree checks: integers zigzag, a bound is `0` or `1, z`)

    linear-robust     bias τ c d (lo hi)×d n w×n
    linear-monotone   j up n w×n
-/

def decWeights : Nat → List Nat → Option (List Int × List Nat)
  | 0, r => some ([], r)
  | n + 1, z :: r => do
    let (ws, r) ← decWeights n r
    pure (Tree.zig z :: ws, r)
  | _ + 1, [] => none

def decRobust (args : List Nat) : Option (Int × Int × Bool × Box × List Int) :=
  match args with
  | zb :: zt :: c :: d :: r => do
    let (B, r) ← Tree.decBox d r
    let (n, r) ← match r with | n :: r => some (n, r) | [] => none
    let (ws, r) ← decWeights n r
    if r.isEmpty && c ≤ 1 then some (Tree.zig zb, Tree.zig zt, c == 1, B, ws) else none
  | _ => none

def decMonotone (args : List Nat) : Option (Nat × Bool × List Int) :=
  match args with
  | j :: up :: n :: r => do
    let (ws, r) ← decWeights n r
    if r.isEmpty && up ≤ 1 then some (j, up == 1, ws) else none
  | _ => none

def runRobust (args : List Nat) : Bool :=
  match decRobust args with
  | some (bias, τ, c, B, ws) => robust bias τ ws B c
  | none => false

def runMonotone (args : List Nat) : Bool :=
  match decMonotone args with
  | some (j, up, ws) => monotone ws j up
  | none => false

def showRobust (args : List Nat) : String :=
  match decRobust args with
  | some (bias, τ, c, B, ws) => s!"bias={bias} tau={τ} approve={c} box=[{Tree.showBox B}] weights={ws.length}"
  | none => "malformed"

def showMonotone (args : List Nat) : String :=
  match decMonotone args with
  | some (j, up, ws) => s!"feature={j} up={up} weights={ws.length}"
  | none => "malformed"

/-! ### Kernel forms

The same checks with the recursors, `cond` and `Option.casesOn`: `if` on a `Bool`, `Option.bind`
and structural recursion each cost the kernel dozens of unfoldings. `*_eq` proves them equal to
the forms above, which the compiled lane runs. -/

def termMinK (w : Int) (b : Bound) : Option Int :=
  cond (intLe 0 w) (cond (intLe w 0) (some 0) (Option.casesOn (motive := fun _ => Option Int) b.lo none fun a => some (Int.mul w a)))
    (Option.casesOn (motive := fun _ => Option Int) b.hi none fun h => some (Int.mul w h))

def termMaxK (w : Int) (b : Bound) : Option Int :=
  cond (intLe 0 w) (cond (intLe w 0) (some 0) (Option.casesOn (motive := fun _ => Option Int) b.hi none fun h => some (Int.mul w h)))
    (Option.casesOn (motive := fun _ => Option Int) b.lo none fun a => some (Int.mul w a))

/-- `t + s` inside `Option`, by cases. -/
def addK (o : Option Int) (r : Option Int) : Option Int :=
  Option.casesOn (motive := fun _ => Option Int) o none fun t =>
    Option.casesOn (motive := fun _ => Option Int) r none fun s => some (Int.add t s)

noncomputable def minScoreK (ws : List Int) : Box → Option Int :=
  List.rec (motive := fun _ => Box → Option Int) (fun _ => some 0)
    (fun w _ ih B => List.casesOn (motive := fun _ => Option Int) B (addK (termMinK w {}) (ih []))
      fun b B' => addK (termMinK w b) (ih B')) ws

noncomputable def maxScoreK (ws : List Int) : Box → Option Int :=
  List.rec (motive := fun _ => Box → Option Int) (fun _ => some 0)
    (fun w _ ih B => List.casesOn (motive := fun _ => Option Int) B (addK (termMaxK w {}) (ih []))
      fun b B' => addK (termMaxK w b) (ih B')) ws

noncomputable def robustK (bias τ : Int) (ws : List Int) (B : Box) (c : Bool) : Bool :=
  cond c (Option.casesOn (motive := fun _ => Bool) (minScoreK ws B) false fun s => intLe τ (Int.add bias s))
    (Option.casesOn (motive := fun _ => Bool) (maxScoreK ws B) false fun s => intLt (Int.add bias s) τ)

theorem termMinK_eq (w : Int) (b : Bound) : termMinK w b = termMin w b := by
  unfold termMinK termMin
  cases intLe 0 w <;> cases intLe w 0 <;> cases b.lo <;> cases b.hi <;> rfl

theorem termMaxK_eq (w : Int) (b : Bound) : termMaxK w b = termMax w b := by
  unfold termMaxK termMax
  cases intLe 0 w <;> cases intLe w 0 <;> cases b.lo <;> cases b.hi <;> rfl

theorem addK_eq (o r : Option Int) : addK o r = o.bind fun t => r.map (t + ·) := by
  cases o <;> cases r <;> rfl

theorem minScoreK_eq (ws : List Int) (B : Box) : minScoreK ws B = minScore ws B := by
  induction ws generalizing B with
  | nil => rfl
  | cons w ws ih =>
    cases B with
    | nil => simp only [minScoreK, minScore] at *; rw [← ih [], addK_eq, termMinK_eq]
    | cons b B => simp only [minScoreK, minScore] at *; rw [← ih B, addK_eq, termMinK_eq]

theorem maxScoreK_eq (ws : List Int) (B : Box) : maxScoreK ws B = maxScore ws B := by
  induction ws generalizing B with
  | nil => rfl
  | cons w ws ih =>
    cases B with
    | nil => simp only [maxScoreK, maxScore] at *; rw [← ih [], addK_eq, termMaxK_eq]
    | cons b B => simp only [maxScoreK, maxScore] at *; rw [← ih B, addK_eq, termMaxK_eq]

/-- The kernel form of the robustness check is the check. -/
theorem robustK_eq (bias τ : Int) (ws : List Int) (B : Box) (c : Bool) :
    robustK bias τ ws B c = robust bias τ ws B c := by
  unfold robustK robust
  rw [minScoreK_eq, maxScoreK_eq]
  cases c <;> simp only [cond_true, cond_false, Bool.false_eq_true, if_true, if_false] <;>
    split <;> simp_all [Int.add_def]

/-- The compiled lane runs the kernel's check on the same decoder's output. -/
theorem runRobust_eq (args : List Nat) :
    runRobust args = match decRobust args with
      | some (bias, τ, c, B, ws) => robustK bias τ ws B c
      | none => false := by
  unfold runRobust
  split <;> simp_all [robustK_eq]

/-! ## Packed robustness: a fixed number of big-integer operations

The model and the box as packed vectors in slots of `B` bits (`d` features): the positive and the
negative parts of the weights, `Wp` and `Wm` (slot `f` is `max(w_f, 0)`, `max(−w_f, 0)`, digits below
`2^mW`), and the box bounds shifted by `O` to be naturals, **reversed** (`LR`, `HR`: slot `d − 1 − f`
is `lo_f + O`, `hi_f + O`, digits below `2^mL`). The least score on the box is
`bias + Σ Wp_f lo_f − Σ Wm_f hi_f`, that is

    bias + slot_{d−1}(Wp · LR) − slot_{d−1}(Wm · HR) − O · (Σ Wp − Σ Wm)

where each slot `d − 1` is a dot product by Kronecker substitution and `Σ W = W mod (2^B − 1)` is a
digit sum. `d · 2^(mW + mL) < 2^B − 1` makes every product slot and every digit sum exact. The
kernel performs about twenty operations, whatever `d`. -/

/-- Slot `d − 1` of a product: the dot product of the two packed vectors. -/
def dotSlot (B d P : Nat) : Nat := Nat.mod (Nat.shiftRight P (Nat.mul B (Nat.sub d 1))) (MLP.pow2 B)

/-- **Packed robustness check.** Approve (`c = true`) on the whole box, or decline on it. -/
def robustPacked (B d mW mL O : Nat) (bias τ : Int) (Wp Wm LR HR : Nat) (c : Bool) : Bool :=
  let σp := Nat.mod Wp (Nat.sub (MLP.pow2 B) 1)
  let σm := Nat.mod Wm (Nat.sub (MLP.pow2 B) 1)
  Nat.ble 1 d && MLP.digitsBelow B d mW Wp && MLP.digitsBelow B d mW Wm &&
    MLP.digitsBelow B d mL LR && MLP.digitsBelow B d mL HR &&
    Nat.blt (Nat.mul d (MLP.pow2 (Nat.add mW mL))) (Nat.sub (MLP.pow2 B) 1) &&
    cond c
      (intLe (Int.add (Int.add τ (Int.ofNat (dotSlot B d (Nat.mul Wm HR)))) (Int.ofNat (Nat.mul O σp)))
        (Int.add (Int.add bias (Int.ofNat (dotSlot B d (Nat.mul Wp LR)))) (Int.ofNat (Nat.mul O σm))))
      (intLt (Int.add (Int.add bias (Int.ofNat (dotSlot B d (Nat.mul Wp HR)))) (Int.ofNat (Nat.mul O σm)))
        (Int.add (Int.add τ (Int.ofNat (dotSlot B d (Nat.mul Wm LR)))) (Int.ofNat (Nat.mul O σp))))

/-- **`linear-robust-packed`** on naturals, as the kernel receives it: the bias and the threshold
zigzag, the decision `c = 1` for approve. -/
def robustPackedN (B d mW mL O zb zt Wp Wm LR HR c : Nat) : Bool :=
  Nat.ble c 1 && robustPacked B d mW mL O (Tree.zig zb) (Tree.zig zt) Wp Wm LR HR (Nat.beq c 1)

/-- The compiled lane of `linear-robust-packed`. -/
def runRobustPacked : List Nat → Bool
  | [B, d, mW, mL, O, zb, zt, Wp, Wm, LR, HR, c] => robustPackedN B d mW mL O zb zt Wp Wm LR HR c
  | _ => false

def showRobustPacked : List Nat → String
  | [B, d, mW, mL, O, zb, zt, _, _, _, _, c] =>
    s!"bias={Tree.zig zb} tau={Tree.zig zt} approve={c == 1} features={d} slot={B} offset={O} weightBits={mW} boundBits={mL}"
  | _ => "malformed"

end OpenTheory.Checks.Linear
