import NN.GraphSpec.Chain.Semantics
import NN.Spec.Core.Context.Real

/-!
# Exact integer networks over TorchLean primitives

A model has two forms.

* The **proof form** is a TorchLean chain, read over `ℝ` by `NN.GraphSpec.Interp.spec`.
* The **check form** is an integer runner on `List ℤ`, which the kernel evaluates quickly.

A `Prim` packages one TorchLean primitive with its integer runner, a Boolean validity check on
its integer parameters, and a proof that the two forms agree. A `Net` is any composition of
`Prim`s. `Net.agrees` proves agreement once for every network, by induction on the
composition: a new architecture built from existing primitives needs no new proof, and a new
primitive needs one agreement lemma.

Further guarantees are contracts: data of kind `C : Prim m n → Type`, one per primitive.
`Net.Rules C g` collects one for every primitive of `g`, so it describes the class of networks
built from primitives that meet `C`. Each contract proves its class theorem once, by the same
induction (for example `Net.box_sound` in `Models.Exact.Interval`).

Scope: vector primitives `[m] → [n]`. Matrix-shaped primitives (attention) are not covered yet.

References: TorchLean, whose chains and primitives are the proof form [@torchlean].
-/

open NN.GraphSpec Spec TorchLean

namespace OpenTheory.Exact

/-- An integer in any TorchLean scalar backend, through its rational cast. -/
def ofInt {α : Type} [Context α] (z : ℤ) : α := ((z : ℚ) : α)

@[simp] theorem ofInt_real (z : ℤ) : (ofInt z : ℝ) = (z : ℝ) :=
  Rat.cast_intCast z

/-- An integer list as a TorchLean vector of length `n`; missing entries read as `0`. -/
def vec {α : Type} [Storage α] [Context α] (n : ℕ) (x : List ℤ) : Tensor α [n] :=
  Tensor.ofFn fun i => ofInt (x.getD i 0)

@[simp] theorem getScalar_vec (n : ℕ) (x : List ℤ) (i : Fin n) :
    (vec n x : Tensor ℝ [n]).getScalar i = (x.getD i 0 : ℝ) := by
  simp [vec]

/-- A TorchLean primitive on vectors with an exact integer runner that agrees with it over `ℝ`.

`embed` reads integer parameters in any TorchLean backend (`ℝ` for proofs, floats for runs).
Agreement is required only for valid parameters (`valid θ = true`) and inputs of length `m`. -/
structure Prim (m n : ℕ) where
  /-- Parameter shapes of the TorchLean primitive. -/
  ps : List Shape
  /-- The TorchLean primitive (proof form). -/
  torch : Primitive ps [m] [n]
  /-- Integer parameters (check form). -/
  Params : Type
  /-- Shape check on the integer parameters, decided by the kernel. -/
  valid : Params → Bool
  /-- Integer forward pass. -/
  run : Params → List ℤ → List ℤ
  /-- The integer parameters as a TorchLean parameter pack, in any backend. -/
  embed : {α : Type} → [Storage α] → [Context α] → Params → TensorPack α ps
  length_run : ∀ θ x, valid θ = true → x.length = m → (run θ x).length = n
  agrees : ∀ θ x, valid θ = true → x.length = m →
    vec n (run θ x) = torch.specFwd (α := ℝ) (embed θ) (vec m x)

/-- Networks built from exact primitives by sequential composition. -/
inductive Net : ℕ → ℕ → Type 1 where
  | prim {m n : ℕ} : Prim m n → Net m n
  | seq {m k n : ℕ} : Net m k → Net k n → Net m n

namespace Net

/-- Parameter shapes of the TorchLean chain. -/
def ps : {m n : ℕ} → Net m n → List Shape
  | _, _, prim p => p.ps
  | _, _, seq f g => f.ps ++ g.ps

/-- The TorchLean chain (proof form). -/
def toChain : {m n : ℕ} → (g : Net m n) → Chain g.ps [m] [n]
  | _, _, prim p => .prim p.torch
  | _, _, seq f g => .seq f.toChain g.toChain

/-- Integer parameters: one entry per primitive, nested like the composition. -/
def Params : {m n : ℕ} → Net m n → Type
  | _, _, prim p => p.Params
  | _, _, seq f g => f.Params × g.Params

/-- Every primitive's parameters pass their shape check. -/
def valid : {m n : ℕ} → (g : Net m n) → g.Params → Bool
  | _, _, prim p, θ => p.valid θ
  | _, _, seq f g, θ => f.valid θ.1 && g.valid θ.2

/-- Integer forward pass (check form). -/
def run : {m n : ℕ} → (g : Net m n) → g.Params → List ℤ → List ℤ
  | _, _, prim p, θ, x => p.run θ x
  | _, _, seq f g, θ, x => g.run θ.2 (f.run θ.1 x)

/-- The integer parameters as a TorchLean parameter pack for `toChain`, in any backend. -/
def embed {α : Type} [Storage α] [Context α] : {m n : ℕ} → (g : Net m n) → g.Params →
    TensorPack α g.ps
  | _, _, prim p, θ => p.embed θ
  | _, _, seq f g, θ => TensorPack.append (f.embed θ.1) (g.embed θ.2)

/-- The real-valued model of `g` with parameters `θ`: TorchLean semantics over `ℝ`. -/
noncomputable def eval {m n : ℕ} (g : Net m n) (θ : g.Params) (x : Tensor ℝ [m]) :
    Tensor ℝ [n] :=
  Interp.spec g.toChain (g.embed θ) x

theorem length_run : {m n : ℕ} → (g : Net m n) → ∀ θ x, g.valid θ = true → x.length = m →
    (g.run θ x).length = n
  | _, _, prim p, θ, x, hθ, hx => p.length_run θ x hθ hx
  | _, _, seq f g, θ, x, hθ, hx => by
      simp only [valid, Bool.and_eq_true] at hθ
      exact g.length_run θ.2 _ hθ.2 (f.length_run θ.1 x hθ.1 hx)

/-- **Agreement for every network.** On valid parameters and an input of length `m`, the
integer runner computes exactly the TorchLean model over `ℝ`. -/
theorem agrees : {m n : ℕ} → (g : Net m n) → ∀ θ x, g.valid θ = true → x.length = m →
    vec n (g.run θ x) = g.eval θ (vec m x)
  | _, _, prim p, θ, x, hθ, hx => by
      simpa [run, eval, toChain, embed, Interp.spec] using p.agrees θ x hθ hx
  | _, _, seq f g, θ, x, hθ, hx => by
      simp only [valid, Bool.and_eq_true] at hθ
      have h₁ := f.agrees θ.1 x hθ.1 hx
      have h₂ := g.agrees θ.2 (f.run θ.1 x) hθ.2 (f.length_run θ.1 x hθ.1 hx)
      simp only [eval, run, toChain, embed, Interp.spec, TensorPack.split_append] at h₁ h₂ ⊢
      rw [h₂, h₁]

/-- One contract of kind `C` for every primitive of `g`: the witness that `g` belongs to the
class of networks built from primitives that meet `C`. -/
def Rules (C : {m n : ℕ} → Prim m n → Type) : {m n : ℕ} → Net m n → Type
  | _, _, prim p => C p
  | _, _, seq f g => Rules C f × Rules C g

end Net

end OpenTheory.Exact
