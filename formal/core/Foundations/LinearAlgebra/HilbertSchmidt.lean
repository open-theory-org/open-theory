import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Hilbert–Schmidt (Frobenius) norm of a linear map

For an orthonormal basis `b` of `E` and `T : E → F`, `hs b T = (Σᵢ ‖T bᵢ‖²)^{1/2}`,
realized as the `L²` norm of the columns `(T bᵢ)ᵢ` in `PiLp 2`, so the triangle
inequality is inherited. Main facts:

* `hs_sq_adjoint`: `hs b T² = hs c (Tᵀ)²` for orthonormal bases `b` of `E`, `c` of `F`
  (so `hs` does not depend on the basis);
* `hs_comp_left_le`: `hs (S ∘ T) ≤ ‖S‖ · hs T`, and `hs_comp_right_le`:
  `hs (T ∘ U) ≤ hs T · ‖U‖` (operator norms);
* `opNorm_le_hs`: `‖T‖ ≤ hs T`.
-/

noncomputable section
open LinearMap

namespace OpenTheory.HilbertSchmidt

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The columns of `T` in the basis `b`, as an `L²` vector. -/
def cols (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) : PiLp 2 (fun _ : ι => F) :=
  WithLp.toLp 2 (fun i => T (b i))

/-- The Hilbert–Schmidt norm in the basis `b`. -/
def hs (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) : ℝ := ‖cols b T‖

theorem hs_nonneg (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) : 0 ≤ hs b T := norm_nonneg _

theorem hs_sq (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) :
    hs b T ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [hs, PiLp.norm_sq_eq_of_L2]; rfl

theorem cols_add (b : OrthonormalBasis ι ℝ E) (T U : E →ₗ[ℝ] F) :
    cols b (T + U) = cols b T + cols b U := rfl

theorem cols_sub (b : OrthonormalBasis ι ℝ E) (T U : E →ₗ[ℝ] F) :
    cols b (T - U) = cols b T - cols b U := rfl

theorem hs_add_le (b : OrthonormalBasis ι ℝ E) (T U : E →ₗ[ℝ] F) :
    hs b (T + U) ≤ hs b T + hs b U := by
  rw [hs, cols_add]; exact norm_add_le _ _

theorem hs_sub_le (b : OrthonormalBasis ι ℝ E) (T U : E →ₗ[ℝ] F) :
    hs b (T - U) ≤ hs b T + hs b U := by
  rw [hs, cols_sub]; exact norm_sub_le _ _

theorem hs_neg (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) : hs b (-T) = hs b T := by
  rw [hs, hs, show cols b (-T) = -cols b T from rfl, norm_neg]

/-- Parseval: `‖x‖² = Σⱼ ⟨cⱼ, x⟩²`. -/
theorem norm_sq_eq_sum (c : OrthonormalBasis κ ℝ F) (x : F) :
    ‖x‖ ^ 2 = ∑ j, inner ℝ (c j) x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← c.sum_inner_mul_inner x x]
  congr 1; funext j; rw [real_inner_comm, sq]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

/-- The operator norm of a linear map between finite-dimensional spaces. -/
def opn (T : E →ₗ[ℝ] F) : ℝ := ‖LinearMap.toContinuousLinearMap T‖

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem norm_apply_le (T : E →ₗ[ℝ] F) (x : E) : ‖T x‖ ≤ opn T * ‖x‖ :=
  (LinearMap.toContinuousLinearMap T).le_opNorm x

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem opn_nonneg (T : E →ₗ[ℝ] F) : 0 ≤ opn T := norm_nonneg _

theorem opn_adjoint (T : E →ₗ[ℝ] F) : opn (LinearMap.adjoint T) = opn T := by
  unfold opn
  rw [LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

/-- **Adjoint swap**: `Σᵢ ‖T bᵢ‖² = Σⱼ ‖Tᵀ cⱼ‖²`. -/
theorem hs_sq_adjoint (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F)
    (T : E →ₗ[ℝ] F) : hs b T ^ 2 = hs c (LinearMap.adjoint T) ^ 2 := by
  rw [hs_sq, hs_sq]
  simp_rw [norm_sq_eq_sum c, norm_sq_eq_sum b]
  rw [Finset.sum_comm]
  congr 1; funext j; congr 1; funext i
  rw [← LinearMap.adjoint_inner_left, real_inner_comm]

theorem hs_sq_basis (b b' : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F)
    (T : E →ₗ[ℝ] F) : hs b T ^ 2 = hs b' T ^ 2 := by
  rw [hs_sq_adjoint b c, hs_sq_adjoint b' c]

theorem hs_adjoint (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F)
    (T : E →ₗ[ℝ] F) : hs b T = hs c (LinearMap.adjoint T) := by
  have := hs_sq_adjoint b c T
  rwa [sq_eq_sq₀ (hs_nonneg _ _) (hs_nonneg _ _)] at this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
theorem hs_comp_left_le (b : OrthonormalBasis ι ℝ E) (S : F →ₗ[ℝ] G) (T : E →ₗ[ℝ] F) :
    hs b (S ∘ₗ T) ≤ opn S * hs b T := by
  rw [← sq_le_sq₀ (hs_nonneg _ _) (mul_nonneg (opn_nonneg _) (hs_nonneg _ _)), mul_pow,
    hs_sq, hs_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [LinearMap.comp_apply, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le S _) 2

theorem hs_comp_right_le (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F)
    (T : E →ₗ[ℝ] F) (U : E →ₗ[ℝ] E) : hs b (T ∘ₗ U) ≤ hs b T * opn U := by
  rw [hs_adjoint b c, hs_adjoint b c T, LinearMap.adjoint_comp, mul_comm, ← opn_adjoint U]
  exact hs_comp_left_le c _ _

omit [FiniteDimensional ℝ F] in
theorem opNorm_le_hs (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] F) : opn T ≤ hs b T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (hs_nonneg _ _) fun x => ?_
  -- ‖T x‖ = ‖Σ ⟨bᵢ, x⟩ T bᵢ‖ ≤ (Σ ‖T bᵢ‖²)^{1/2} ‖x‖ by Cauchy–Schwarz
  have hx : x = ∑ i, inner ℝ (b i) x • b i := (b.sum_repr' x).symm
  have h1 : ‖T x‖ ≤ ∑ i, |inner ℝ (b i) x| * ‖T (b i)‖ := by
    conv_lhs => rw [hx, map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    congr 1; funext i; rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 : ∑ i, |inner ℝ (b i) x| * ‖T (b i)‖ ≤
      √(∑ i, |inner ℝ (b i) x| ^ 2) * √(∑ i, ‖T (b i)‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h3 : √(∑ i, |inner ℝ (b i) x| ^ 2) = ‖x‖ := by
    rw [show (∑ i, |inner ℝ (b i) x| ^ 2) = ‖x‖ ^ 2 by
      rw [norm_sq_eq_sum b]; congr 1; funext i; rw [sq_abs]]
    exact Real.sqrt_sq (norm_nonneg x)
  have h4 : √(∑ i, ‖T (b i)‖ ^ 2) = hs b T := by
    rw [← hs_sq]; exact Real.sqrt_sq (hs_nonneg _ _)
  calc ‖LinearMap.toContinuousLinearMap T x‖ = ‖T x‖ := rfl
    _ ≤ hs b T * ‖x‖ := by rw [h3, h4] at h2; linarith [h1.trans h2]

end OpenTheory.HilbertSchmidt
