import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn

/-! An executable, integer-valued one-hidden-layer ReLU MLP. All weights and
biases are represented in the finite code; no learned decoder parameters exist.
Biases are multiplied by fixed positive scales chosen with the architecture.
Division by positive layer scales is omitted because it cannot change the
argmax. Equal scores choose the first class.

Evaluation traverses the weight list once, row by row, so that kernel checks of
error counts scale linearly in the number of parameters. Inputs shorter than
the architecture are padded with zeros; extra inputs are ignored. -/

namespace OpenTheory.QuantizedMLP

abbrev Code (p q : ℕ) := Fin p → Fin q

/-- A one-hidden-layer integer ReLU architecture, fixed before training. -/
structure Arch where
  inputs : ℕ
  hidden : ℕ
  classes : ℕ
  hiddenBiasScale : ℤ
  outputBiasScale : ℤ

/-- Both weight matrices and both bias vectors are charged. -/
def Arch.parameterCount (a : Arch) : ℕ :=
  a.inputs * a.hidden + a.hidden + a.hidden * a.classes + a.classes

/-- Pooled 4×4 digit inputs in `[0,64]`, four hidden units, ten classes. -/
def digits16 : Arch := ⟨16, 4, 10, 64, 128⟩

/-- Integer weights `-2, -1, 0, 1` of a code, in storage order. -/
def weights {p : ℕ} (code : Code p 4) : List ℤ := List.ofFn fun i => ((code i : ℕ) : ℤ) - 2

def dot (ws xs : List ℤ) : ℤ := (List.zipWith (· * ·) ws xs).sum

/-- `r` consecutive rows of length `k`. -/
def rows (k : ℕ) : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | r + 1, ws => ws.take k :: rows k r (ws.drop k)

/-- Storage order: hidden weights by unit, hidden biases, output weights by
class, output biases. -/
def scoresOfWeights (a : Arch) (ws x : List ℤ) : List ℤ :=
  let d := a.inputs
  let h := a.hidden
  let c := a.classes
  let rest := ws.drop (d * h)
  let out := rest.drop h
  let hidden := List.zipWith (fun row b => max 0 (dot row x + a.hiddenBiasScale * b))
    (rows d h ws) (rest.take h)
  List.zipWith (fun row b => dot row hidden + a.outputBiasScale * b)
    (rows h c out) ((out.drop (h * c)).take c)

/-- First index attaining the maximum score. -/
def argmaxFirst (scores : List ℤ) : ℕ :=
  (scores.zipIdx.foldl (fun best candidate =>
    if best.1 < candidate.1 then candidate else best) (scores.headD 0, 0)).2

abbrev Observation := List ℤ × ℕ

def errorBitOfWeights (a : Arch) (ws : List ℤ) (z : Observation) : ℕ :=
  if argmaxFirst (scoresOfWeights a ws z.1) = z.2 then 0 else 1

def errorCountOfWeights (a : Arch) (ws : List ℤ) (rows : List Observation) : ℕ :=
  (rows.map (errorBitOfWeights a ws)).sum

def logits (a : Arch) (code : Code a.parameterCount 4) (x : List ℤ) : List ℤ :=
  scoresOfWeights a (weights code) x

def predict (a : Arch) (code : Code a.parameterCount 4) (x : List ℤ) : ℕ :=
  argmaxFirst (logits a code x)

def errorBit (a : Arch) (code : Code a.parameterCount 4) (z : Observation) : ℕ :=
  errorBitOfWeights a (weights code) z

def errorCount (a : Arch) (code : Code a.parameterCount 4) (rows : List Observation) : ℕ :=
  errorCountOfWeights a (weights code) rows

theorem errorCount_append (a : Arch) (code : Code a.parameterCount 4)
    (xs ys : List Observation) :
    errorCount a code (xs ++ ys) = errorCount a code xs + errorCount a code ys := by
  simp [errorCount, errorCountOfWeights, List.map_append, List.sum_append]

/-- Decode an artifact into the finite hypothesis type. The external verifier
rejects invalid entries; modulo also makes this total for arbitrary lists. -/
def codeOfList (p : ℕ) (xs : List ℕ) : Code p 4 :=
  fun i => ⟨(xs[i.val]?.getD 0) % 4, Nat.mod_lt _ (by decide)⟩

/-- The integer weights of a decoded artifact, computed without indexing. -/
def weightsOfList (xs : List ℕ) : List ℤ := xs.map fun v => ((v % 4 : ℕ) : ℤ) - 2

theorem weights_codeOfList {p : ℕ} (xs : List ℕ) (hlen : xs.length = p) :
    weights (codeOfList p xs) = weightsOfList xs := by
  apply List.ext_getElem
  · simp [weights, weightsOfList, hlen]
  · intro i h1 h2
    have hi : i < xs.length := by simpa [weightsOfList] using h2
    simp [weights, weightsOfList, codeOfList, List.getElem?_eq_getElem hi]

/-- Kernel checks of saved networks go through the linear-time list form. -/
theorem errorCount_codeOfList (a : Arch) (xs : List ℕ) (hlen : xs.length = a.parameterCount)
    (rows : List Observation) :
    errorCount a (codeOfList _ xs) rows = errorCountOfWeights a (weightsOfList xs) rows := by
  rw [errorCount, weights_codeOfList xs hlen]

end OpenTheory.QuantizedMLP
