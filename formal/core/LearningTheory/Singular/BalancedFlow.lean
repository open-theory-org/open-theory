import LearningTheory.Singular.RiccatiLimit
import LearningTheory.Singular.PlateauEstimator
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Balanced gradient flow solves the Riccati equation

For the two-layer linear network, stack `Z = [Aᵀ; B]` (rows indexed by `Fin M ⊕ Fin N`). Along
gradient flow on `½‖B A - C‖²`, the imbalance `A Aᵀ - Bᵀ B` is conserved (`gap_const`). If it
vanishes initially (balanced start), then `Ż = S Z - ½ Z Zᵀ Z` with `S = [[0, Cᵀ], [C, 0]]`
(`Zmat_grad`), so `P = Z Zᵀ` solves `Ṗ = S P + P S - P²` (`hasDerivAt_Pop`). The network product
`B A` is the off-diagonal block of `P`.
-/

noncomputable section
open Real Filter Topology Matrix
open scoped RealInnerProductSpace

namespace OpenTheory.Plateau

variable {M N H : ℕ}

/-- `A` as a matrix. -/
def Amat (p : State M N H) : Matrix (Fin H) (Fin M) ℝ := Matrix.of p.1
/-- `B` as a matrix. -/
def Bmat (p : State M N H) : Matrix (Fin N) (Fin H) ℝ := Matrix.of p.2

/-- The imbalance `A Aᵀ - Bᵀ B`. -/
def gap (p : State M N H) : Matrix (Fin H) (Fin H) ℝ := Amat p * (Amat p)ᵀ - (Bmat p)ᵀ * Bmat p

theorem Amat_grad (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    Amat (gradField C p) = (Bmat p)ᵀ * (C - Bmat p * Amat p) := by
  rw [Amat, gradField_eq_matrix]; rfl

theorem Bmat_grad (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    Bmat (gradField C p) = (C - Bmat p * Amat p) * (Amat p)ᵀ := by
  rw [Bmat, gradField_eq_matrix]; rfl

/-- The derivative of the imbalance vanishes. -/
theorem gap_deriv_zero (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    Amat (gradField C p) * (Amat p)ᵀ + Amat p * (Amat (gradField C p))ᵀ -
      ((Bmat (gradField C p))ᵀ * Bmat p + (Bmat p)ᵀ * Bmat (gradField C p)) = 0 := by
  rw [Amat_grad, Bmat_grad]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  abel

/-- **Conservation of balance.** -/
theorem gap_const (C : Matrix (Fin N) (Fin M) ℝ) {f : ℝ → State M N H}
    (hf : ∀ t, HasDerivAt f (gradField C (f t)) t) (t : ℝ) : gap (f t) = gap (f 0) := by
  ext l m
  have hA : ∀ s (k : Fin H) (j : Fin M), HasDerivAt (fun s => (f s).1 k j)
      ((gradField C (f s)).1 k j) s := fun s k j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 (hf s).fst k) j
  have hB : ∀ s (i : Fin N) (k : Fin H), HasDerivAt (fun s => (f s).2 i k)
      ((gradField C (f s)).2 i k) s := fun s i k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 (hf s).snd i) k
  have hd : ∀ s, HasDerivAt (fun s => gap (f s) l m) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => ∑ j, (f s).1 l j * (f s).1 m j)
        (∑ j, ((gradField C (f s)).1 l j * (f s).1 m j + (f s).1 l j * (gradField C (f s)).1 m j))
        s := HasDerivAt.fun_sum fun j _ => (hA s l j).mul (hA s m j)
    have h2 : HasDerivAt (fun s => ∑ i, (f s).2 i l * (f s).2 i m)
        (∑ i, ((gradField C (f s)).2 i l * (f s).2 i m + (f s).2 i l * (gradField C (f s)).2 i m))
        s := HasDerivAt.fun_sum fun i _ => (hB s i l).mul (hB s i m)
    have h := h1.sub h2
    have e := congrFun (congrFun (gap_deriv_zero C (f s)) l) m
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply, Amat, Bmat, Matrix.of_apply] at e
    refine (h.congr_deriv ?_)
    rw [← e]
    simp only [Finset.sum_add_distrib]
  have hconst := is_const_of_deriv_eq_zero (f := fun s => gap (f s) l m)
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv)
  have := hconst t 0
  simpa [gap, Amat, Bmat, Matrix.sub_apply, Matrix.mul_apply] using this

/-- `Z = [Aᵀ; B]`. -/
def Zmat (p : State M N H) : Matrix (Fin M ⊕ Fin N) (Fin H) ℝ :=
  Matrix.fromRows (Amat p)ᵀ (Bmat p)

/-- The dilation `[[0, Cᵀ], [C, 0]]`. -/
def Smat (C : Matrix (Fin N) (Fin M) ℝ) : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) ℝ :=
  Matrix.fromBlocks 0 Cᵀ C 0

theorem Zmat_transpose_mul (p : State M N H) :
    (Zmat p)ᵀ * Zmat p = Amat p * (Amat p)ᵀ + (Bmat p)ᵀ * Bmat p := by
  rw [Zmat, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_transpose]

theorem Smat_transpose (C : Matrix (Fin N) (Fin M) ℝ) : (Smat C)ᵀ = Smat C := by
  rw [Smat, Matrix.fromBlocks_transpose]; simp

/-- **The stacked dynamics** under balance: `Ż = S Z - Z (Bᵀ B)`. -/
theorem Zmat_grad (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) (hbal : gap p = 0) :
    Zmat (gradField C p) = Smat C * Zmat p - Zmat p * ((Bmat p)ᵀ * Bmat p) := by
  have hb : Amat p * (Amat p)ᵀ = (Bmat p)ᵀ * Bmat p := sub_eq_zero.1 hbal
  rw [Zmat, Zmat, Amat_grad, Bmat_grad, Smat, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  simp only [Matrix.zero_mul, zero_add, add_zero, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [← hb]
  simp only [← Matrix.mul_assoc]
  ext (i | i) j <;> simp [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, sub_eq_add_neg]

/-! ### Operators -/

/-- A matrix as a continuous linear map between Euclidean spaces. -/
def cl {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (X : Matrix m n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  LinearMap.toContinuousLinearMap (toEuclideanLin X)

section Cl

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq m] in
theorem cl_mul (X : Matrix m n ℝ) (Y : Matrix n l ℝ) : cl (X * Y) = cl X ∘L cl Y := by
  ext v; simp [cl]

omit [DecidableEq m] in
theorem cl_add (X Y : Matrix m n ℝ) : cl (X + Y) = cl X + cl Y := by
  ext v; simp [cl]

omit [DecidableEq m] in
theorem cl_sub (X Y : Matrix m n ℝ) : cl (X - Y) = cl X - cl Y := by
  ext v; simp [cl]

omit [DecidableEq m] in
theorem cl_smul (c : ℝ) (X : Matrix m n ℝ) : cl (c • X) = c • cl X := by
  ext v; simp [cl]

theorem adjoint_cl (X : Matrix m n ℝ) : ContinuousLinearMap.adjoint (cl X) = cl Xᵀ := by
  ext v
  have := congrArg (fun L : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n => L v)
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint X)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  simp only [cl, LinearMap.coe_toContinuousLinearMap']
  rw [this]
  rfl

end Cl

local notation "VS" => EuclideanSpace ℝ (Fin M ⊕ Fin N)
local notation "HS" => EuclideanSpace ℝ (Fin H)

/-- `p ↦ [Aᵀ; B]` is linear. -/
def ZL : State M N H →ₗ[ℝ] (HS →L[ℝ] VS) where
  toFun p := cl (Zmat p)
  map_add' p q := by
    rw [← cl_add]; congr 1
    ext (i | i) j <;> simp [Zmat, Amat, Bmat, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  map_smul' c p := by
    rw [RingHom.id_apply, ← cl_smul]; congr 1
    ext (i | i) j <;> simp [Zmat, Amat, Bmat, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]

theorem hasDerivAt_ZL (C : Matrix (Fin N) (Fin M) ℝ) {f : ℝ → State M N H}
    (hf : ∀ t, HasDerivAt f (gradField C (f t)) t) (t : ℝ) :
    HasDerivAt (fun s => cl (Zmat (f s))) (cl (Zmat (gradField C (f t)))) t :=
  (LinearMap.toContinuousLinearMap (ZL (M := M) (N := N) (H := H))).hasFDerivAt.comp_hasDerivAt t (hf t)

/-- `P = Z Zᵀ` as an operator. -/
def Pop (p : State M N H) : VS →L[ℝ] VS := cl (Zmat p) ∘L ContinuousLinearMap.adjoint (cl (Zmat p))

/-- **Balanced flow solves the Riccati equation** with `S` the dilation of `C`. -/
theorem hasDerivAt_Pop (C : Matrix (Fin N) (Fin M) ℝ) {f : ℝ → State M N H}
    (hf : ∀ t, HasDerivAt f (gradField C (f t)) t) (hbal : gap (f 0) = 0) (t : ℝ) :
    HasDerivAt (fun s => Pop (f s)) (Riccati.ricField (cl (Smat C)) (Pop (f t))) t := by
  have hZ := hasDerivAt_ZL C hf t
  have hZt : HasDerivAt (fun s => ContinuousLinearMap.adjoint (cl (Zmat (f s))))
      (ContinuousLinearMap.adjoint (cl (Zmat (gradField C (f t))))) t := by
    let T : (HS →L[ℝ] VS) →L[ℝ] (VS →L[ℝ] HS) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun L => ContinuousLinearMap.adjoint L
          map_add' := fun a b => map_add _ a b
          map_smul' := fun c a => by simp }
    exact T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ZL C hf t)
  have h := hZ.clm_comp hZt
  refine h.congr_deriv ?_
  have hb : gap (f t) = 0 := (gap_const C hf t).trans hbal
  rw [Zmat_grad C (f t) hb]
  simp only [Riccati.ricField, Pop, adjoint_cl]
  set Z := Zmat (f t)
  set Mb := (Bmat (f t))ᵀ * Bmat (f t)
  have hM : Mbᵀ = Mb := by simp [Mb, Matrix.transpose_mul]
  have h2M : Zᵀ * Z = (2 : ℝ) • Mb := by
    rw [Zmat_transpose_mul, sub_eq_zero.1 hb, two_smul]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Smat_transpose, hM, cl_sub, cl_mul]
  have hP2 : cl Z ∘L cl Zᵀ ∘L (cl Z ∘L cl Zᵀ) = (2 : ℝ) • (cl Z ∘L cl Mb ∘L cl Zᵀ) := by
    rw [← cl_mul, ← cl_mul, ← cl_mul, ← cl_mul, ← cl_mul, ← cl_smul]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, h2M]
    simp [Mb, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  simp only [ContinuousLinearMap.comp_assoc] at hP2 ⊢
  rw [hP2]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_assoc]
  rw [two_smul ℝ (cl Z ∘L cl Mb ∘L cl Zᵀ)]
  abel

end OpenTheory.Plateau
