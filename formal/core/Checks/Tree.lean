/-!
# Tree-ensemble checks (core Lean only)

A decision tree on integer-scaled features: a node sends an input to `lo` when its feature is at
most the threshold, to `hi` otherwise (the LightGBM/XGBoost convention `x f ≤ t`). An ensemble's
score is a base plus the sum of its trees' leaves. A box gives each feature optional closed bounds;
a feature without an entry is unbounded.

The checks never evaluate the model on an input. They walk each tree, keeping only the branches a
point of the box can reach (each split tested against the box itself), and verify untrusted
witnesses given as literals [@chen2019robustness; @devos2021versatile]:

* `robustCert`: a bound per tree, every leaf the box reaches within it, and `base + Σ bounds` on
  one side of the decision threshold `τ`;
* `monotoneCert`: a cut per split on feature `j`, every reachable leaf below the threshold at most
  the cut and every reachable leaf above it at least (reversed if decreasing).

Any witness that passes gives a sound result; the producer (`methods/trees/`) computes the best
ones. They are sufficient conditions, proved sound once (`Scopes/TreeRegion.lean`); a rejection is
not a counterexample. Testing each split against the box rather than the box narrowed by the
splits above it loses nothing on a trained tree, where every path is satisfiable on its own.
-/

namespace OpenTheory.Checks.Tree

/-- A decision tree with integer thresholds and integer leaves. -/
inductive Tree where
  | leaf (v : Int)
  | node (f : Nat) (t : Int) (lo hi : Tree)

/-- Optional closed bounds on one feature. -/
structure Bound where
  lo : Option Int := none
  hi : Option Int := none

/-- Bounds per feature; a feature past the end of the list is unbounded. -/
abbrev Box := List Bound

def Box.get : Box → Nat → Bound
  | [], _ => {}
  | b :: _, 0 => b
  | _ :: B, f + 1 => Box.get B f

/-- Some point of the box can satisfy `x f ≤ t`. -/
def lowOk (B : Box) (f : Nat) (t : Int) : Bool :=
  match (B.get f).lo with
  | none => true
  | some a => decide (a ≤ t)

/-- Some point of the box can satisfy `t < x f`. -/
def highOk (B : Box) (f : Nat) (t : Int) : Bool :=
  match (B.get f).hi with
  | none => true
  | some b => decide (t < b)

/-- Every leaf a point of the box reaches is at most `m`. -/
def Tree.allLe (B : Box) (m : Int) : Tree → Bool
  | .leaf v => decide (v ≤ m)
  | .node f t l r => (!lowOk B f t || l.allLe B m) && (!highOk B f t || r.allLe B m)

/-- Every leaf a point of the box reaches is at least `m`. -/
def Tree.allGe (B : Box) (m : Int) : Tree → Bool
  | .leaf v => decide (m ≤ v)
  | .node f t l r => (!lowOk B f t || l.allGe B m) && (!highOk B f t || r.allGe B m)

/-- Cuts for a monotonicity certificate, one per node, in the shape of the tree. -/
inductive Cuts where
  | none
  | cut (c : Int) (lo hi : Cuts)

/-- Monotonicity in feature `j` with the cuts as witnesses: at every reachable split on `j`, the
low side's leaves are at most the cut and the high side's at least (reversed if decreasing). -/
def Tree.monoCut (B : Box) (j : Nat) (up : Bool) : Tree → Cuts → Bool
  | .leaf _, _ => true
  | .node _ _ _ _, .none => false
  | .node f t l r, .cut c cl cr =>
    (!lowOk B f t || l.monoCut B j up cl) && (!highOk B f t || r.monoCut B j up cr) &&
    (!(Nat.beq f j) || !lowOk B f t || !highOk B f t ||
      (if up then l.allLe B c && r.allGe B c else l.allGe B c && r.allLe B c))

/-- `base + Σ bounds`, and every tree within its bound on the box (at most if `hi`, at least
otherwise). `false` if the two lists differ in length. -/
def withinAll (B : Box) (hi : Bool) : List Tree → List Int → Bool
  | [], [] => true
  | t :: ts, m :: ms => (if hi then t.allLe B m else t.allGe B m) && withinAll B hi ts ms
  | _, _ => false

def sumInt : List Int → Int
  | [] => 0
  | m :: ms => m + sumInt ms

/-- **Robustness certificate.** `ms` bounds each tree on the box: from below for `c = true`
(every score is at least `τ`), from above for `c = false` (every score is below `τ`). -/
def robustCert (base τ : Int) (ts : List Tree) (ms : List Int) (B : Box) (c : Bool) : Bool :=
  (if c then decide (τ ≤ base + sumInt ms) else decide (base + sumInt ms < τ)) &&
    withinAll B (!c) ts ms

/-- **Monotonicity certificate.** Every tree is monotone in `j` on the box, with its cuts. -/
def monotoneCert (j : Nat) (up : Bool) (ts : List Tree) (cs : List Cuts) (B : Box) : Bool :=
  match ts, cs with
  | [], [] => true
  | t :: ts, c :: cs => t.monoCut B j up c && monotoneCert j up ts cs B
  | _, _ => false

/-! ### Kernel forms

The same checks written with the recursors (`Tree.rec`, `List.rec`), which the kernel reduces in
one step per node, and with integer comparisons by cases down to `Nat.ble`: structural recursion,
the `Decidable` instances and `if` on a `Bool` each cost the kernel dozens of unfoldings. The
structural forms above run in the compiled lane; `*_eq` proves the two equal. -/

/-- `a ≤ b` on integers by cases, down to the kernel's `Nat.ble`: the `Decidable` and `LE`
instances cost the kernel dozens of unfoldings per comparison. -/
def intLe (a b : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) a
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun n => Nat.ble m n) fun _ => false)
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun _ => true) fun n => Nat.ble n m)

/-- `a < b` on integers, as `a + 1 ≤ b`. -/
def intLt (a b : Int) : Bool := intLe (Int.add a 1) b

theorem intLe_eq (a b : Int) : intLe a b = decide (a ≤ b) := by
  cases a <;> cases b <;> simp only [intLe] <;> rw [Bool.eq_iff_iff] <;> simp
  all_goals omega

theorem intLt_eq (a b : Int) : intLt a b = decide (a < b) := by
  rw [intLt, intLe_eq]
  exact decide_eq_decide.mpr (by change a + 1 ≤ b ↔ a < b; omega)

/-- `Box.get` with the list recursor. -/
noncomputable def Box.getK (B : Box) : Nat → Bound :=
  List.rec (motive := fun _ => Nat → Bound) (fun _ => {})
    (fun b _ ih f => Nat.casesOn (motive := fun _ => Bound) f b fun g => ih g) B

noncomputable def lowOkK (B : Box) (f : Nat) (t : Int) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (B.getK f).lo true fun a => intLe a t

noncomputable def highOkK (B : Box) (f : Nat) (t : Int) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (B.getK f).hi true fun b => intLt t b

/-- The two reachability tests of a split, from one lookup of its feature's bounds. -/
noncomputable def splitK (B : Box) (f : Nat) (t : Int) (k : Bool → Bool → Bool) : Bool :=
  Bound.casesOn (motive := fun _ => Bool) (B.getK f) fun lo hi =>
    k (Option.casesOn (motive := fun _ => Bool) lo true fun a => intLe a t)
      (Option.casesOn (motive := fun _ => Bool) hi true fun b => intLt t b)

noncomputable def Tree.allLeK (B : Box) (m : Int) (T : Tree) : Bool :=
  Tree.rec (motive := fun _ => Bool) (fun v => intLe v m)
    (fun f t _ _ il ir => splitK B f t fun lo hi => (!lo || il) && (!hi || ir)) T

noncomputable def Tree.allGeK (B : Box) (m : Int) (T : Tree) : Bool :=
  Tree.rec (motive := fun _ => Bool) (fun v => intLe m v)
    (fun f t _ _ il ir => splitK B f t fun lo hi => (!lo || il) && (!hi || ir)) T

noncomputable def Tree.monoCutK (B : Box) (j : Nat) (up : Bool) (T : Tree) : Cuts → Bool :=
  Tree.rec (motive := fun _ => Cuts → Bool) (fun _ _ => true)
    (fun f t l r il ir cs => Cuts.casesOn (motive := fun _ => Bool) cs false fun c cl cr =>
      splitK B f t fun lo hi =>
        (!lo || il cl) && (!hi || ir cr) &&
        (!(Nat.beq f j) || !lo || !hi ||
          (cond up (l.allLeK B c && r.allGeK B c) (l.allGeK B c && r.allLeK B c)))) T

noncomputable def withinAllK (B : Box) (hi : Bool) (ts : List Tree) : List Int → Bool :=
  List.rec (motive := fun _ => List Int → Bool)
    (fun ms => List.casesOn (motive := fun _ => Bool) ms true fun _ _ => false)
    (fun t _ ih ms => List.casesOn (motive := fun _ => Bool) ms false fun m ms =>
      (cond hi (t.allLeK B m) (t.allGeK B m)) && ih ms) ts

noncomputable def sumIntK (ms : List Int) : Int :=
  List.rec (motive := fun _ => Int) (Int.ofNat 0) (fun m _ ih => Int.add m ih) ms

noncomputable def robustCertK (base τ : Int) (ts : List Tree) (ms : List Int) (B : Box) (c : Bool) : Bool :=
  (cond c (intLe τ (Int.add base (sumIntK ms))) (intLt (Int.add base (sumIntK ms)) τ)) &&
    withinAllK B (!c) ts ms

noncomputable def monotoneCertK (j : Nat) (up : Bool) (ts : List Tree) (B : Box) : List Cuts → Bool :=
  List.rec (motive := fun _ => List Cuts → Bool)
    (fun cs => List.casesOn (motive := fun _ => Bool) cs true fun _ _ => false)
    (fun t _ ih cs => List.casesOn (motive := fun _ => Bool) cs false fun c cs =>
      t.monoCutK B j up c && ih cs) ts

theorem Box.getK_eq (B : Box) (f : Nat) : B.getK f = B.get f := by
  induction B generalizing f with
  | nil => rfl
  | cons b B ih =>
    cases f with
    | zero => rfl
    | succ g => exact ih g

theorem lowOkK_eq (B : Box) (f : Nat) (t : Int) : lowOkK B f t = lowOk B f t := by
  simp only [lowOkK, lowOk, Box.getK_eq]; cases (B.get f).lo <;> simp [intLe_eq]

theorem highOkK_eq (B : Box) (f : Nat) (t : Int) : highOkK B f t = highOk B f t := by
  simp only [highOkK, highOk, Box.getK_eq]; cases (B.get f).hi <;> simp [intLt_eq]

theorem splitK_eq (B : Box) (f : Nat) (t : Int) (k : Bool → Bool → Bool) :
    splitK B f t k = k (lowOk B f t) (highOk B f t) := by
  rw [← lowOkK_eq, ← highOkK_eq]
  simp only [splitK, lowOkK, highOkK]

theorem Tree.allLeK_eq (B : Box) (m : Int) (T : Tree) : T.allLeK B m = T.allLe B m := by
  induction T with
  | leaf v => simp [Tree.allLeK, Tree.allLe, intLe_eq]
  | node f t l r il ir => simp only [Tree.allLeK, Tree.allLe, splitK_eq] at *; rw [il, ir]

theorem Tree.allGeK_eq (B : Box) (m : Int) (T : Tree) : T.allGeK B m = T.allGe B m := by
  induction T with
  | leaf v => simp [Tree.allGeK, Tree.allGe, intLe_eq]
  | node f t l r il ir => simp only [Tree.allGeK, Tree.allGe, splitK_eq] at *; rw [il, ir]

theorem Tree.monoCutK_eq (B : Box) (j : Nat) (up : Bool) (T : Tree) (cs : Cuts) :
    T.monoCutK B j up cs = T.monoCut B j up cs := by
  induction T generalizing cs with
  | leaf v => rfl
  | node f t l r il ir =>
    cases cs with
    | none => rfl
    | cut c cl cr =>
      simp only [Tree.monoCutK, Tree.monoCut, splitK_eq, Tree.allLeK_eq, Tree.allGeK_eq, cond_eq_ite] at *
      rw [il, ir]

theorem withinAllK_eq (B : Box) (hi : Bool) (ts : List Tree) (ms : List Int) :
    withinAllK B hi ts ms = withinAll B hi ts ms := by
  induction ts generalizing ms with
  | nil => cases ms <;> rfl
  | cons t ts ih =>
    cases ms with
    | nil => rfl
    | cons m ms => simp only [withinAllK, withinAll, Tree.allLeK_eq, Tree.allGeK_eq, cond_eq_ite] at *; rw [ih]

theorem sumIntK_eq (ms : List Int) : sumIntK ms = sumInt ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [sumIntK, sumInt] at *; rw [← ih]; rfl

/-- The kernel form of the robustness certificate is the certificate. -/
theorem robustCertK_eq (base τ : Int) (ts : List Tree) (ms : List Int) (B : Box) (c : Bool) :
    robustCertK base τ ts ms B c = robustCert base τ ts ms B c := by
  simp only [robustCertK, robustCert, sumIntK_eq, withinAllK_eq, intLe_eq, intLt_eq, cond_eq_ite,
    Int.add_def]

/-- The kernel form of the monotonicity certificate is the certificate. -/
theorem monotoneCertK_eq (j : Nat) (up : Bool) (ts : List Tree) (cs : List Cuts) (B : Box) :
    monotoneCertK j up ts B cs = monotoneCert j up ts cs B := by
  induction ts generalizing cs with
  | nil => cases cs <;> rfl
  | cons t ts ih =>
    cases cs with
    | nil => rfl
    | cons c cs => simp only [monotoneCertK, monotoneCert, Tree.monoCutK_eq] at *; rw [ih]

/-! ## Requests as natural numbers

Both lanes receive a request as a list of naturals and decode it here, so they check the same
trees. An integer `z` is sent zigzag (`2z` if `z ≥ 0`, `−2z − 1` otherwise); a bound is `0`
(none) or `1, z`; a tree is `0, z` (leaf) or `1, f, z, low, high` (node, preorder); cuts are `0`
or `1, z, low, high`.

    tree-robust     base τ c d (lo hi)×d n (tree m)×n          c: 1 approve, 0 decline
    tree-monotone   j up d (lo hi)×d n (tree cuts)×n           up: 1 increasing, 0 decreasing
-/

def zig (n : Nat) : Int := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def decBound : List Nat → Option (Option Int × List Nat)
  | 0 :: r => some (none, r)
  | 1 :: z :: r => some (some (zig z), r)
  | _ => none

def decBox : Nat → List Nat → Option (Box × List Nat)
  | 0, r => some ([], r)
  | d + 1, r => do
    let (lo, r) ← decBound r
    let (hi, r) ← decBound r
    let (B, r) ← decBox d r
    pure ({ lo, hi } :: B, r)

/-- A tree in preorder; `fuel` bounds the depth. -/
def decTree : Nat → List Nat → Option (Tree × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: z :: r => some (.leaf (zig z), r)
  | fuel + 1, 1 :: f :: z :: r => do
    let (l, r) ← decTree fuel r
    let (h, r) ← decTree fuel r
    pure (.node f (zig z) l h, r)
  | _, _ => none

def decCuts : Nat → List Nat → Option (Cuts × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: r => some (.none, r)
  | fuel + 1, 1 :: z :: r => do
    let (l, r) ← decCuts fuel r
    let (h, r) ← decCuts fuel r
    pure (.cut (zig z) l h, r)
  | _, _ => none

/-- `n` trees, each followed by its bound. -/
def decBounded (fuel : Nat) : Nat → List Nat → Option (List Tree × List Int × List Nat)
  | 0, r => some ([], [], r)
  | n + 1, r => do
    let (t, r) ← decTree fuel r
    let (m, r) ← match r with | z :: r => some (zig z, r) | [] => none
    let (ts, ms, r) ← decBounded fuel n r
    pure (t :: ts, m :: ms, r)

/-- `n` trees, each followed by its cuts. -/
def decCut (fuel : Nat) : Nat → List Nat → Option (List Tree × List Cuts × List Nat)
  | 0, r => some ([], [], r)
  | n + 1, r => do
    let (t, r) ← decTree fuel r
    let (c, r) ← decCuts fuel r
    let (ts, cs, r) ← decCut fuel n r
    pure (t :: ts, c :: cs, r)

/-- A robustness request: `(base, τ, c, box, trees, bounds)`, the whole list consumed. -/
def decRobust (args : List Nat) : Option (Int × Int × Bool × Box × List Tree × List Int) :=
  match args with
  | zb :: zt :: c :: d :: r => do
    let (B, r) ← decBox d r
    let (n, r) ← match r with | n :: r => some (n, r) | [] => none
    let (ts, ms, r) ← decBounded args.length n r
    if r.isEmpty && c ≤ 1 then some (zig zb, zig zt, c == 1, B, ts, ms) else none
  | _ => none

/-- A monotonicity request: `(j, up, box, trees, cuts)`, the whole list consumed. -/
def decMonotone (args : List Nat) : Option (Nat × Bool × Box × List Tree × List Cuts) :=
  match args with
  | j :: up :: d :: r => do
    let (B, r) ← decBox d r
    let (n, r) ← match r with | n :: r => some (n, r) | [] => none
    let (ts, cs, r) ← decCut args.length n r
    if r.isEmpty && up ≤ 1 then some (j, up == 1, B, ts, cs) else none
  | _ => none

/-- The compiled lane of `tree-robust`. -/
def runRobust (args : List Nat) : Bool :=
  match decRobust args with
  | some (base, τ, c, B, ts, ms) => robustCert base τ ts ms B c
  | none => false

/-- The compiled lane of `tree-monotone`. -/
def runMonotone (args : List Nat) : Bool :=
  match decMonotone args with
  | some (j, up, B, ts, cs) => monotoneCert j up ts cs B
  | none => false

end OpenTheory.Checks.Tree
