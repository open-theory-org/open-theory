import OpenTheory.Optimization.MatrixSpectralPreconditioning
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Phase 18 Module 1: Operator & Matrix Newton–Schulz Orthogonalization, Singular-Value Cubic Convergence, and Bochner Measure-Theoretic Gradient Noise Scale

This module upgrades the scalar algebraic proxies of `OpenTheory.MatrixSpectralPreconditioning`
to genuine **matrix operators** (`Matrix (Fin m) (Fin n) ℝ`), **exact singular-value polynomial
dynamics**, **$2 \times 2$ symmetric matrix eigen-decomposition**, and **Hilbert-space +
measure-theoretic Bochner gradient variance decomposition** with **zero `sorry`s**:

1. **Part 1: Matrix Newton–Schulz Polynomial Operator on `Matrix (Fin m) (Fin n) ℝ` & Orthogonal Isometry Fixed-Point Theorem
   (`matrixNewtonSchulzStep`, `IsRowOrthonormalMatrix`, `IsColOrthonormalMatrix`,
   `matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal`,
   `matrixNewtonSchulzStep_fixed_point_of_colOrthonormal`,
   `matrixNewtonSchulzStep_commutes_with_orthogonal`)**:
   - Defines the cubic matrix Newton–Schulz operator $X \mapsto \frac{3}{2} X - \frac{1}{2} X X^\top X$
     used in Muon / matrix orthogonalization.
   - Proves that every row-orthonormal matrix ($X X^\top = I_m$) and every column-orthonormal
     matrix ($X^\top X = I_n$) is an exact fixed point of `matrixNewtonSchulzStep`.
   - Proves orthogonal equivariance: for any column-orthonormal $U$ ($U^\top U = I$) and
     row-orthonormal $V$ ($V V^\top = I$),
     `matrixNewtonSchulzStep (U * Σ * V) = U * (matrixNewtonSchulzStep Σ) * V`.

2. **Part 2: Exact Singular-Value Cubic Convergence of Newton–Schulz
   (`newtonSchulzSingularMap`, `diagonal_matrixNewtonSchulzStep`,
   `newtonSchulz_singular_cubic_convergence_and_basin`)**:
   - Defines the singular-value cubic polynomial $p(\sigma) = \frac{3}{2}\sigma - \frac{1}{2}\sigma^3$.
   - Proves the exact cubic residual factorization $1 - p(\sigma) = \frac{1}{2}(1 - \sigma)^2(2 + \sigma)$,
     unit fixed point $p(1) = 1$, positivity on $(0, \sqrt{3})$, strict monotonic attraction toward $1$
     with quadratic contraction $1 - p(\sigma) < \frac{3}{2}(1 - \sigma)^2$ on $(0, 1)$, and the exact
     action of `matrixNewtonSchulzStep` on diagonal matrices `Matrix.diagonal d`.

3. **Part 3: Coupled $2 \times 2$ Symmetric Curvature Matrix (`coupledCurvatureMatrix2x2`) Eigen-Decomposition
   (`coupledCurvatureMatrix2x2`, `plusMode2`, `minusMode2`,
   `coupledCurvatureMatrix2x2_eigenvalues_and_condition_number`)**:
   - Defines the explicit $2 \times 2$ symmetric coupled curvature matrix
     `coupledCurvatureMatrix2x2 ρ_off = !![1, ρ_off; ρ_off, 1]` and eigenmodes
     `plusMode2 = ![1, 1]` and `minusMode2 = ![1, -1]`.
   - Proves the exact matrix-vector eigenvalue equations
     `coupledCurvatureMatrix2x2 ρ_off *ᵥ plusMode2 = (1 + ρ_off) • plusMode2` and
     `coupledCurvatureMatrix2x2 ρ_off *ᵥ minusMode2 = (1 - ρ_off) • minusMode2`,
     together with `det = 1 - ρ_off ^ 2`, `trace = 2`, and the exact bridge showing the eigenvalue
     ratio `(1 + ρ_off) / (1 - ρ_off)` equals `diagonalPrecondConditionNumber ρ_off`.

4. **Part 4: Bochner Measure-Theoretic & Hilbert-Space Gradient Noise Scale & Mini-Batch Variance Reduction
   (`hilbert_pairwise_orthogonal_norm_sq_sum`, `hilbert_minibatch_variance_reduction_law`,
   `measureGradVariance`, `measureCriticalBatchCoordinate`,
   `measure_stochastic_gradient_second_moment_decomposition`)**:
   - Proves in any real inner product space `H` that the mini-batch average of $B$ pairwise
     orthogonal zero-mean gradient noise vectors $\xi_i$ with uniform energy $\|\xi_i\|^2 = \sigma_{\mathrm{noise}}^2$
     satisfies $\|(1/B)\sum_{i=1}^B \xi_i\|^2 = \sigma_{\mathrm{noise}}^2 / B$, and that the
     signal-to-noise crossover $\sigma_{\mathrm{noise}}^2 / B = \|G\|^2$ holds iff
     $(B : \mathbb{R}) = \text{criticalBatchSize } \sigma_{\mathrm{noise}}^2 \|G\|^2$.
   - Proves on any probability space $(\Omega, \mu)$ (`[IsProbabilityMeasure μ]`) the Bochner
     second-moment decomposition $\int g(\omega)^2\,d\mu = (\int g\,d\mu)^2 + \mathrm{Var}_\mu(g)$
     and grounds `criticalBatchSize` in `measureGradVariance μ g / (∫ g ∂μ)^2`.

5. **Part 5: Grand Operator Newton–Schulz & Measure-Theoretic Noise Scale Theorem
   (`operator_newton_schulz_and_noise_scale_grand_theorem`)**:
   - Unites Parts 1–4 into a single end-to-end theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix

namespace OpenTheory.OperatorNewtonSchulzAndNoiseScale

open OpenTheory
open OpenTheory.OptimalTrainingRegimes
open OpenTheory.AlgorithmicOptimizerUnimprovability
open OpenTheory.FastestTrainingAndRoofline
open OpenTheory.MatrixSpectralPreconditioning

/-! ## Part 1: Matrix Newton–Schulz Polynomial Operator & Orthogonal Isometry Fixed-Point Theorem -/

/-- **Matrix Newton–Schulz Cubic Orthogonalization Operator (`matrixNewtonSchulzStep`)**:
The Muon / Newton–Schulz cubic matrix iteration on `X : Matrix (Fin m) (Fin n) ℝ`:
`matrixNewtonSchulzStep X = (3 / 2 : ℝ) • X - (1 / 2 : ℝ) • (X * Xᵀ * X)`. -/
def matrixNewtonSchulzStep {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  (3 / 2 : ℝ) • X - (1 / 2 : ℝ) • (X * Xᵀ * X)

/-- **Row-Orthonormal Matrix Predicate (`IsRowOrthonormalMatrix`)**:
A matrix `X : Matrix (Fin m) (Fin n) ℝ` has orthonormal rows when `X * Xᵀ = 1`. -/
def IsRowOrthonormalMatrix {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  X * Xᵀ = 1

/-- **Column-Orthonormal Matrix Predicate (`IsColOrthonormalMatrix`)**:
A matrix `X : Matrix (Fin m) (Fin n) ℝ` has orthonormal columns when `Xᵀ * X = 1`. -/
def IsColOrthonormalMatrix {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Xᵀ * X = 1

/-- **Theorem 1a (Row-Orthonormal Fixed Point: `matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal`)**:
Every row-orthonormal matrix `X` (`X * Xᵀ = 1`) is an exact fixed point of `matrixNewtonSchulzStep`. -/
theorem matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℝ) (hX : IsRowOrthonormalMatrix X) :
    matrixNewtonSchulzStep X = X := by
  unfold matrixNewtonSchulzStep
  rw [hX, Matrix.one_mul, ← sub_smul]
  norm_num

/-- **Theorem 1a' (Column-Orthonormal Fixed Point: `matrixNewtonSchulzStep_fixed_point_of_colOrthonormal`)**:
Every column-orthonormal matrix `X` (`Xᵀ * X = 1`) is an exact fixed point of `matrixNewtonSchulzStep`. -/
theorem matrixNewtonSchulzStep_fixed_point_of_colOrthonormal {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℝ) (hX : IsColOrthonormalMatrix X) :
    matrixNewtonSchulzStep X = X := by
  unfold matrixNewtonSchulzStep
  rw [Matrix.mul_assoc, hX, Matrix.mul_one, ← sub_smul]
  norm_num

/-- **Theorem 1b (Orthogonal Equivariance of Matrix Newton–Schulz: `matrixNewtonSchulzStep_commutes_with_orthogonal`)**:
For any column-orthonormal `U : Matrix (Fin m) (Fin m) ℝ` (`Uᵀ * U = 1`), any rectangular matrix
`S : Matrix (Fin m) (Fin n) ℝ`, and any row-orthonormal `V : Matrix (Fin n) (Fin n) ℝ` (`V * Vᵀ = 1`),
the matrix Newton–Schulz operator commutes with orthogonal transformations:
`matrixNewtonSchulzStep (U * S * V) = U * (matrixNewtonSchulzStep S) * V`. -/
theorem matrixNewtonSchulzStep_commutes_with_orthogonal {m n : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) (S : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsColOrthonormalMatrix U) (hV : IsRowOrthonormalMatrix V) :
    matrixNewtonSchulzStep (U * S * V) = U * matrixNewtonSchulzStep S * V := by
  have hU_eq : Uᵀ * U = 1 := hU
  have hV_eq : V * Vᵀ = 1 := hV
  have htrans : (U * S * V)ᵀ = Vᵀ * Sᵀ * Uᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hcubic :
      (U * S * V) * (U * S * V)ᵀ * (U * S * V) = U * (S * Sᵀ * S) * V := by
    rw [htrans]
    calc
      (U * S * V) * (Vᵀ * Sᵀ * Uᵀ) * (U * S * V)
        = U * S * (V * Vᵀ) * Sᵀ * (Uᵀ * U) * S * V := by
            simp only [Matrix.mul_assoc]
      _ = U * (S * Sᵀ * S) * V := by
            rw [hV_eq, hU_eq]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
  unfold matrixNewtonSchulzStep
  rw [hcubic]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-! ## Part 2: Exact Singular-Value Cubic Convergence of Newton–Schulz (`newtonSchulzSingularMap`) -/

/-- **Newton–Schulz Singular-Value Cubic Polynomial (`newtonSchulzSingularMap`)**:
Induced scalar polynomial on singular values $\sigma \mapsto \frac{3}{2}\sigma - \frac{1}{2}\sigma^3$. -/
def newtonSchulzSingularMap (σ : ℝ) : ℝ :=
  (3 / 2 : ℝ) * σ - (1 / 2 : ℝ) * σ ^ 3

@[simp]
theorem newtonSchulzSingularMap_zero : newtonSchulzSingularMap 0 = 0 := by
  unfold newtonSchulzSingularMap
  norm_num

@[simp]
theorem newtonSchulzSingularMap_one : newtonSchulzSingularMap 1 = 1 := by
  unfold newtonSchulzSingularMap
  norm_num

/-- **Action of `matrixNewtonSchulzStep` on Diagonal Matrices (`diagonal_matrixNewtonSchulzStep`)**:
Applying `matrixNewtonSchulzStep` to `Matrix.diagonal d` applies `newtonSchulzSingularMap`
entrywise to each diagonal singular value `d i`. -/
theorem diagonal_matrixNewtonSchulzStep {n : ℕ} (d : Fin n → ℝ) :
    matrixNewtonSchulzStep (Matrix.diagonal d) =
      Matrix.diagonal (fun i => newtonSchulzSingularMap (d i)) := by
  unfold matrixNewtonSchulzStep newtonSchulzSingularMap
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij,
      smul_eq_mul, mul_zero, sub_zero]

/-- **Theorem 2: Exact Singular-Value Cubic Convergence & Basin of Attraction of Newton–Schulz
(`newtonSchulz_singular_cubic_convergence_and_basin`)**:
1. **Exact Cubic Residual Factorization Identity**:
   `1 - newtonSchulzSingularMap σ = (1 / 2 : ℝ) * (1 - σ) ^ 2 * (2 + σ)` and
   `newtonSchulzSingularMap σ - 1 = -(1 / 2 : ℝ) * (σ - 1) ^ 2 * (σ + 2)`.
2. **Unit Fixed Point & Positivity Basin on `(0, √3)`**:
   `newtonSchulzSingularMap 1 = 1`, and for `0 < σ` and `σ ^ 2 < 3`,
   `0 < newtonSchulzSingularMap σ`.
3. **Strict Monotonicity Toward `1` & Quadratic Contraction on `(0, 1)`**:
   For `0 < σ` and `σ < 1`:
   - `σ < newtonSchulzSingularMap σ` and `newtonSchulzSingularMap σ < 1`,
   - `0 < 1 - newtonSchulzSingularMap σ`,
   - `1 - newtonSchulzSingularMap σ < (3 / 2 : ℝ) * (1 - σ) ^ 2`.
4. **Action on Diagonal Matrices**:
   `matrixNewtonSchulzStep (Matrix.diagonal d) = Matrix.diagonal (fun i => newtonSchulzSingularMap (d i))`. -/
theorem newtonSchulz_singular_cubic_convergence_and_basin (σ : ℝ) :
    (1 - newtonSchulzSingularMap σ = (1 / 2 : ℝ) * (1 - σ) ^ 2 * (2 + σ) ∧
      newtonSchulzSingularMap σ - 1 = -(1 / 2 : ℝ) * (σ - 1) ^ 2 * (σ + 2)) ∧
    (newtonSchulzSingularMap 1 = 1 ∧
      (0 < σ → σ ^ 2 < 3 → 0 < newtonSchulzSingularMap σ)) ∧
    (0 < σ → σ < 1 →
      σ < newtonSchulzSingularMap σ ∧
      newtonSchulzSingularMap σ < 1 ∧
      0 < 1 - newtonSchulzSingularMap σ ∧
      1 - newtonSchulzSingularMap σ < (3 / 2 : ℝ) * (1 - σ) ^ 2) ∧
    (∀ {n : ℕ} (d : Fin n → ℝ),
      matrixNewtonSchulzStep (Matrix.diagonal d) =
        Matrix.diagonal (fun i => newtonSchulzSingularMap (d i))) := by
  have hres1 : 1 - newtonSchulzSingularMap σ = (1 / 2 : ℝ) * (1 - σ) ^ 2 * (2 + σ) := by
    unfold newtonSchulzSingularMap
    ring
  have hres2 : newtonSchulzSingularMap σ - 1 = -(1 / 2 : ℝ) * (σ - 1) ^ 2 * (σ + 2) := by
    unfold newtonSchulzSingularMap
    ring
  refine ⟨⟨hres1, hres2⟩, ⟨newtonSchulzSingularMap_one, ?_⟩, ?_, fun d => diagonal_matrixNewtonSchulzStep d⟩
  · intro hσ_pos hσ_sq
    have hfactor : newtonSchulzSingularMap σ = (σ / 2) * (3 - σ ^ 2) := by
      unfold newtonSchulzSingularMap
      ring
    rw [hfactor]
    have h3 : 0 < 3 - σ ^ 2 := by linarith
    positivity
  · intro hσ_pos hσ_lt1
    have h1_sub_pos : 0 < 1 - σ := by linarith
    have h1_add_pos : 0 < 1 + σ := by linarith
    have h2_add_pos : 0 < 2 + σ := by linarith
    have hdiff_sigma : newtonSchulzSingularMap σ - σ = (σ / 2) * (1 - σ) * (1 + σ) := by
      unfold newtonSchulzSingularMap
      ring
    have hgt_sigma : σ < newtonSchulzSingularMap σ := by
      have hpos : 0 < newtonSchulzSingularMap σ - σ := by
        rw [hdiff_sigma]
        positivity
      linarith
    have hres_pos : 0 < 1 - newtonSchulzSingularMap σ := by
      rw [hres1]
      positivity
    have hlt_one : newtonSchulzSingularMap σ < 1 := by linarith
    have hquad_bound : 1 - newtonSchulzSingularMap σ < (3 / 2 : ℝ) * (1 - σ) ^ 2 := by
      have hdiff_bound :
          (3 / 2 : ℝ) * (1 - σ) ^ 2 - (1 - newtonSchulzSingularMap σ) =
            (1 / 2 : ℝ) * (1 - σ) ^ 3 := by
        unfold newtonSchulzSingularMap
        ring
      have hpos : 0 < (3 / 2 : ℝ) * (1 - σ) ^ 2 - (1 - newtonSchulzSingularMap σ) := by
        rw [hdiff_bound]
        positivity
      linarith
    exact ⟨hgt_sigma, hlt_one, hres_pos, hquad_bound⟩

/-! ## Part 3: Coupled $2 \times 2$ Symmetric Curvature Matrix (`coupledCurvatureMatrix2x2`) Eigen-Decomposition -/

/-- **Coupled $2 \times 2$ Symmetric Curvature Matrix (`coupledCurvatureMatrix2x2`)**:
Explicit $2 \times 2$ matrix operator `!![1, ρ_off; ρ_off, 1]` representing a diagonally
preconditioned coupled neuron/channel block with unit diagonal curvatures and off-diagonal
correlation `ρ_off`. -/
def coupledCurvatureMatrix2x2 (ρ_off : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, ρ_off; ρ_off, 1]

/-- **Symmetric Principal Eigenmode (`plusMode2`)**:
Vector `![1, 1]` in `Fin 2 → ℝ` with eigenvalue `1 + ρ_off`. -/
def plusMode2 : Fin 2 → ℝ :=
  ![1, 1]

/-- **Antisymmetric Minor Eigenmode (`minusMode2`)**:
Vector `![1, -1]` in `Fin 2 → ℝ` with eigenvalue `1 - ρ_off`. -/
def minusMode2 : Fin 2 → ℝ :=
  ![1, -1]

/-- **Theorem 3: Eigen-Decomposition, Determinant, Trace, and Condition Number Bridge for
`coupledCurvatureMatrix2x2` (`coupledCurvatureMatrix2x2_eigenvalues_and_condition_number`)**:
For any cross-channel correlation `ρ_off : ℝ`:
1. `coupledCurvatureMatrix2x2 ρ_off *ᵥ plusMode2 = (1 + ρ_off) • plusMode2`,
2. `coupledCurvatureMatrix2x2 ρ_off *ᵥ minusMode2 = (1 - ρ_off) • minusMode2`,
3. `Matrix.det (coupledCurvatureMatrix2x2 ρ_off) = 1 - ρ_off ^ 2` (which equals `diagonalSpectralDeterminantFactor ρ_off`),
4. `Matrix.trace (coupledCurvatureMatrix2x2 ρ_off) = 2`,
5. The ratio of its exact eigenvalues `(1 + ρ_off) / (1 - ρ_off)` equals
   `diagonalPrecondConditionNumber ρ_off`. -/
theorem coupledCurvatureMatrix2x2_eigenvalues_and_condition_number (ρ_off : ℝ) :
    coupledCurvatureMatrix2x2 ρ_off *ᵥ plusMode2 = (1 + ρ_off) • plusMode2 ∧
    coupledCurvatureMatrix2x2 ρ_off *ᵥ minusMode2 = (1 - ρ_off) • minusMode2 ∧
    Matrix.det (coupledCurvatureMatrix2x2 ρ_off) = 1 - ρ_off ^ 2 ∧
    Matrix.det (coupledCurvatureMatrix2x2 ρ_off) = diagonalSpectralDeterminantFactor ρ_off ∧
    Matrix.trace (coupledCurvatureMatrix2x2 ρ_off) = 2 ∧
    (1 + ρ_off) / (1 - ρ_off) = diagonalPrecondConditionNumber ρ_off := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · ext i
    fin_cases i
    · simp [coupledCurvatureMatrix2x2, plusMode2, Matrix.mulVec]
    · simp [coupledCurvatureMatrix2x2, plusMode2, Matrix.mulVec]
      ring
  · ext i
    fin_cases i
    · simp [coupledCurvatureMatrix2x2, minusMode2, Matrix.mulVec]
      ring
    · simp [coupledCurvatureMatrix2x2, minusMode2, Matrix.mulVec]
      ring
  · simp [coupledCurvatureMatrix2x2, Matrix.det_fin_two]
    ring
  · simp [coupledCurvatureMatrix2x2, diagonalSpectralDeterminantFactor, Matrix.det_fin_two]
    ring
  · simp [coupledCurvatureMatrix2x2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring

/-! ## Part 4: Bochner Measure-Theoretic & Hilbert-Space Gradient Noise Scale & Mini-Batch Variance Reduction -/

/-- **Pythagorean Norm-Square Identity for Pairwise Orthogonal Vectors on a Finset
(`hilbert_pairwise_orthogonal_norm_sq_sum`)**:
In any real inner product space `H`, if a family `ξ : ι → H` is pairwise orthogonal on a finset `s`
(`∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪ξ i, ξ j⟫ = 0`), then
`‖∑ i ∈ s, ξ i‖ ^ 2 = ∑ i ∈ s, ‖ξ i‖ ^ 2`. -/
theorem hilbert_pairwise_orthogonal_norm_sq_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (ξ : ι → H)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪ξ i, ξ j⟫ = 0) :
    ‖∑ i ∈ s, ξ i‖ ^ 2 = ∑ i ∈ s, ‖ξ i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have horth_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪ξ i, ξ j⟫ = 0 := by
      intro i hi j hj hij
      exact horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcross : ⟪ξ a, ∑ i ∈ s, ξ i⟫ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      exact horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) hne
    rw [norm_add_sq_real, hcross, ih horth_s]
    ring

/-- **Theorem 4a: Hilbert-Space Pairwise Orthogonal Mini-Batch Variance Reduction & Critical Batch Crossover
(`hilbert_minibatch_variance_reduction_law`)**:
In any real inner product space `H`, given true gradient `G : H` and `B : ℕ` pairwise orthogonal
zero-mean stochastic gradient noise vectors `ξ : Fin B → H` with uniform noise energy
`∀ i, ‖ξ i‖ ^ 2 = σ_noise_sq`:
1. **Exact $1/B$ Mini-Batch Variance Reduction**:
   For `0 < B`, `‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = σ_noise_sq / (B : ℝ)`.
2. **Exact Signal-to-Noise Critical Batch Size Crossover (`↔`)**:
   For `0 < B` and `‖G‖ ≠ 0`, the mini-batch noise variance equals the squared true gradient norm
   (`‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = ‖G‖ ^ 2`) **if and only if**
   `(B : ℝ) = criticalBatchSize σ_noise_sq (‖G‖ ^ 2)`. -/
theorem hilbert_minibatch_variance_reduction_law
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {B : ℕ} (hB : 0 < B) (G : H) (ξ : Fin B → H) (σ_noise_sq : ℝ)
    (horth : ∀ i j : Fin B, i ≠ j → ⟪ξ i, ξ j⟫ = 0)
    (hvar : ∀ i : Fin B, ‖ξ i‖ ^ 2 = σ_noise_sq) :
    ‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = σ_noise_sq / (B : ℝ) ∧
    (‖G‖ ≠ 0 →
      (‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = ‖G‖ ^ 2 ↔
        (B : ℝ) = criticalBatchSize σ_noise_sq (‖G‖ ^ 2))) := by
  have hB_pos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hB_pos
  have hsum_sq : ‖∑ i : Fin B, ξ i‖ ^ 2 = (B : ℝ) * σ_noise_sq := by
    rw [hilbert_pairwise_orthogonal_norm_sq_sum Finset.univ ξ (fun i _ j _ hij => horth i j hij)]
    simp [hvar]
  have hbatch_var : ‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = σ_noise_sq / (B : ℝ) := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity), hsum_sq]
    field_simp [hB_ne]
  refine ⟨hbatch_var, ?_⟩
  intro hG_ne
  have hG_sq_ne : ‖G‖ ^ 2 ≠ 0 := pow_ne_zero 2 hG_ne
  rw [hbatch_var]
  unfold criticalBatchSize
  constructor
  · intro heq
    have hmul : σ_noise_sq = ‖G‖ ^ 2 * (B : ℝ) := (div_eq_iff hB_ne).mp heq
    exact (eq_div_iff hG_sq_ne).mpr (by linarith)
  · intro hB_eq
    have hmul : (B : ℝ) * ‖G‖ ^ 2 = σ_noise_sq := (eq_div_iff hG_sq_ne).mp hB_eq
    exact (div_eq_iff hB_ne).mpr (by linarith)

/-- **Measure-Theoretic Bochner Gradient Variance (`measureGradVariance`)**:
On a measure space `(Ω, μ)`, the Bochner variance of a scalar stochastic gradient coordinate
`g : Ω → ℝ` around its Bochner expectation `∫ x, g x ∂μ`:
`measureGradVariance μ g = ∫ ω, (g ω - ∫ x, g x ∂μ) ^ 2 ∂μ`. -/
def measureGradVariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  ∫ ω, (g ω - ∫ x, g x ∂μ) ^ 2 ∂μ

/-- **Measure-Theoretic Critical Batch Size Coordinate (`measureCriticalBatchCoordinate`)**:
Noise-to-signal ratio `measureGradVariance μ g / (∫ ω, g ω ∂μ) ^ 2` of a Bochner-integrable
stochastic gradient coordinate `g : Ω → ℝ` on `(Ω, μ)`. -/
def measureCriticalBatchCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  measureGradVariance μ g / (∫ ω, g ω ∂μ) ^ 2

/-- **Theorem 4b: Measure-Theoretic Bochner Second-Moment Gradient Decomposition
(`measure_stochastic_gradient_second_moment_decomposition`)**:
On any probability space `(Ω, μ)` (`[IsProbabilityMeasure μ]`), for any stochastic gradient
coordinate `g : Ω → ℝ` satisfying `Integrable g μ` and `Integrable (fun ω => (g ω) ^ 2) μ`:
1. **Nonnegativity of Bochner Gradient Variance**:
   `0 ≤ measureGradVariance μ g`.
2. **Exact Bochner Second-Moment Bias–Variance Decomposition**:
   `∫ ω, (g ω) ^ 2 ∂μ = (∫ ω, g ω ∂μ) ^ 2 + measureGradVariance μ g`.
3. **Exact Bridge to `criticalBatchSize`**:
   `measureCriticalBatchCoordinate μ g = criticalBatchSize (measureGradVariance μ g) ((∫ ω, g ω ∂μ) ^ 2)`. -/
theorem measure_stochastic_gradient_second_moment_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Integrable g μ) (hg2 : Integrable (fun ω => (g ω) ^ 2) μ) :
    0 ≤ measureGradVariance μ g ∧
    ∫ ω, (g ω) ^ 2 ∂μ = (∫ ω, g ω ∂μ) ^ 2 + measureGradVariance μ g ∧
    measureCriticalBatchCoordinate μ g =
      criticalBatchSize (measureGradVariance μ g) ((∫ ω, g ω ∂μ) ^ 2) := by
  set m : ℝ := ∫ x, g x ∂μ
  have hvar_nonneg : 0 ≤ measureGradVariance μ g := by
    unfold measureGradVariance
    exact integral_nonneg fun ω => sq_nonneg _
  have hlin_int : Integrable (fun ω => 2 * m * g ω) μ := hg.const_mul (2 * m)
  have hconst_int : Integrable (fun _ : Ω => m ^ 2) μ := integrable_const (m ^ 2)
  have hsub_int : Integrable (fun ω => (g ω) ^ 2 - 2 * m * g ω) μ := hg2.sub hlin_int
  have hexpand :
      (fun ω => (g ω - m) ^ 2) = fun ω => (g ω) ^ 2 - 2 * m * g ω + m ^ 2 := by
    ext ω
    ring
  have hvar_eq : measureGradVariance μ g = (∫ ω, (g ω) ^ 2 ∂μ) - m ^ 2 := by
    unfold measureGradVariance
    change (∫ ω, (g ω - m) ^ 2 ∂μ) = (∫ ω, (g ω) ^ 2 ∂μ) - m ^ 2
    rw [hexpand, integral_add hsub_int hconst_int, integral_sub hg2 hlin_int,
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    change (∫ ω, (g ω) ^ 2 ∂μ) - 2 * m * m + m ^ 2 = (∫ ω, (g ω) ^ 2 ∂μ) - m ^ 2
    ring
  refine ⟨hvar_nonneg, ?_, rfl⟩
  linarith

/-! ## Part 5: Grand Operator Newton–Schulz & Measure-Theoretic Noise Scale Theorem -/

/-- **Theorem 5: Grand Operator Newton–Schulz & Measure-Theoretic Noise Scale Synthesis
(`operator_newton_schulz_and_noise_scale_grand_theorem`)**:
Unites Parts 1–4 in a single theorem:
1. **Matrix Newton–Schulz Orthogonal Isometry Fixed Point & Equivariance**:
   Row-orthonormal and column-orthonormal matrices are exact fixed points of `matrixNewtonSchulzStep`,
   and `matrixNewtonSchulzStep` commutes with orthogonal transformations `U * Σ * V`.
2. **Singular-Value Cubic Convergence & Diagonal Matrix Action**:
   For `0 < σ < 1`, `σ < newtonSchulzSingularMap σ < 1` with cubic residual factorization
   `1 - newtonSchulzSingularMap σ = (1 / 2) * (1 - σ) ^ 2 * (2 + σ) < (3 / 2) * (1 - σ) ^ 2`,
   and `matrixNewtonSchulzStep (Matrix.diagonal d) = Matrix.diagonal (fun i => newtonSchulzSingularMap (d i))`.
3. **Explicit $2 \times 2$ Coupled Curvature Matrix Eigen-Decomposition**:
   `coupledCurvatureMatrix2x2 ρ_off` has eigenvectors `plusMode2` (`1 + ρ_off`) and `minusMode2` (`1 - ρ_off`),
   determinant `1 - ρ_off ^ 2`, trace `2`, and eigenvalue ratio `diagonalPrecondConditionNumber ρ_off`.
4. **Hilbert-Space $1/B$ Mini-Batch Variance Law & Bochner Second-Moment Decomposition**:
   Pairwise orthogonal noise vectors satisfy `‖(1 / B) • ∑ ξ_i‖ ^ 2 = σ_noise_sq / B` with
   crossover iff `B = criticalBatchSize σ_noise_sq (‖G‖ ^ 2)`, and any square-integrable gradient
   coordinate on `(Ω, μ)` satisfies `∫ g^2 ∂μ = (∫ g ∂μ)^2 + measureGradVariance μ g`. -/
theorem operator_newton_schulz_and_noise_scale_grand_theorem
    {m n B : ℕ} (hB : 0 < B)
    (X : Matrix (Fin m) (Fin n) ℝ) (hX_row : IsRowOrthonormalMatrix X)
    (σ ρ_off : ℝ) (hσ_pos : 0 < σ) (hσ_lt1 : σ < 1)
    (d : Fin n → ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H) (ξ : Fin B → H) (σ_noise_sq : ℝ)
    (horth : ∀ i j : Fin B, i ≠ j → ⟪ξ i, ξ j⟫ = 0)
    (hvar : ∀ i : Fin B, ‖ξ i‖ ^ 2 = σ_noise_sq)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Integrable g μ) (hg2 : Integrable (fun ω => (g ω) ^ 2) μ) :
    matrixNewtonSchulzStep X = X ∧
    (1 - newtonSchulzSingularMap σ = (1 / 2 : ℝ) * (1 - σ) ^ 2 * (2 + σ) ∧
      σ < newtonSchulzSingularMap σ ∧
      newtonSchulzSingularMap σ < 1 ∧
      1 - newtonSchulzSingularMap σ < (3 / 2 : ℝ) * (1 - σ) ^ 2 ∧
      matrixNewtonSchulzStep (Matrix.diagonal d) =
        Matrix.diagonal (fun i => newtonSchulzSingularMap (d i))) ∧
    (coupledCurvatureMatrix2x2 ρ_off *ᵥ plusMode2 = (1 + ρ_off) • plusMode2 ∧
      coupledCurvatureMatrix2x2 ρ_off *ᵥ minusMode2 = (1 - ρ_off) • minusMode2 ∧
      Matrix.det (coupledCurvatureMatrix2x2 ρ_off) = 1 - ρ_off ^ 2 ∧
      Matrix.trace (coupledCurvatureMatrix2x2 ρ_off) = 2 ∧
      (1 + ρ_off) / (1 - ρ_off) = diagonalPrecondConditionNumber ρ_off) ∧
    (‖(1 / (B : ℝ)) • ∑ i : Fin B, ξ i‖ ^ 2 = σ_noise_sq / (B : ℝ) ∧
      0 ≤ measureGradVariance μ g ∧
      ∫ ω, (g ω) ^ 2 ∂μ = (∫ ω, g ω ∂μ) ^ 2 + measureGradVariance μ g ∧
      measureCriticalBatchCoordinate μ g =
        criticalBatchSize (measureGradVariance μ g) ((∫ ω, g ω ∂μ) ^ 2)) := by
  have hfp := matrixNewtonSchulzStep_fixed_point_of_rowOrthonormal X hX_row
  obtain ⟨⟨hres1, _⟩, _, hbasin, hdiag⟩ := newtonSchulz_singular_cubic_convergence_and_basin σ
  obtain ⟨hgt, hlt1, _, hquad⟩ := hbasin hσ_pos hσ_lt1
  obtain ⟨heig_plus, heig_minus, hdet, _, htrace, hcond⟩ :=
    coupledCurvatureMatrix2x2_eigenvalues_and_condition_number ρ_off
  obtain ⟨hbatch_var, _⟩ :=
    hilbert_minibatch_variance_reduction_law hB G ξ σ_noise_sq horth hvar
  obtain ⟨hvar_nonneg, hbochner, hcrit_coord⟩ :=
    measure_stochastic_gradient_second_moment_decomposition μ g hg hg2
  exact ⟨hfp,
    ⟨hres1, hgt, hlt1, hquad, hdiag d⟩,
    ⟨heig_plus, heig_minus, hdet, htrace, hcond⟩,
    ⟨hbatch_var, hvar_nonneg, hbochner, hcrit_coord⟩⟩

end OpenTheory.OperatorNewtonSchulzAndNoiseScale
