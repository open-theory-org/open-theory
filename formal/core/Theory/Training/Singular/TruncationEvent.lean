import Theory.Training.Singular.TruncationRank
import SLT.MatrixInfra.Perturb

/-!
# The good event: small noise fixes the spectral picture

If `‖C Cᵀ - W Wᵀ‖ ≤ h` and every nonzero eigenvalue of `W Wᵀ` is `≥ s2`, Weyl's
inequality (vendored SLT) puts every eigenvalue of `C Cᵀ` in `(-∞, h] ∪ [s2 - h, ∞)`
(`eigen_split`). Consequences, for `h < τ < s2 - h`:

* the number of eigenvalues `≥ τ` of `C Cᵀ` is the rank count of `W` (`count_eq_of_close`);
* an eigenvector of `C Cᵀ` with eigenvalue `μ` has `μ ≥ s2 - h` or `μ ≤ h`
  (`eigenvalue_split`), by Rayleigh bounds on spectral subspaces;
* at most `count` orthonormal vectors fit in the spectral subspace (`card_le_count`).
-/

noncomputable section
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRank

namespace OpenTheory.TruncationEvent

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →ₗ[ℝ] E} {n : ℕ}

theorem inner_eq_sum_eigen (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) (x : E) :
    ⟪A x, x⟫ = ∑ i, hA.eigenvalues hn i * ⟪hA.eigenvectorBasis hn i, x⟫ ^ 2 := by
  set v := hA.eigenvectorBasis hn
  rw [← v.sum_inner_mul_inner (A x) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪A x, v i⟫ = hA.eigenvalues hn i * ⟪v i, x⟫ := by
    rw [hA x (v i), hA.apply_eigenvectorBasis hn i, RCLike.ofReal_real_eq_id, id_eq,
      real_inner_smul_right, real_inner_comm]
  rw [h1]; ring

/-- Lower Rayleigh bound on a spectral subspace. -/
theorem le_inner_of_mem' (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) {S : Set ℝ} {a : ℝ}
    (ha : ∀ i, hA.eigenvalues hn i ∈ S → a ≤ hA.eigenvalues hn i) {x : E}
    (hx : x ∈ hA.spectralSubspace hn S) : a * ‖x‖ ^ 2 ≤ ⟪A x, x⟫ := by
  rw [inner_eq_sum_eigen hA hn, norm_sq_eq_sum (hA.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hA.eigenvalues hn i ∈ S
  · exact mul_le_mul_of_nonneg_right (ha i hi) (sq_nonneg _)
  · have h0 := hA.eigenvectorBasis_repr_eq_zero_of_mem_spectralSubspace hn hi hx
    rw [OrthonormalBasis.repr_apply_apply] at h0
    simp [h0]

/-- Upper Rayleigh bound on a spectral subspace. -/
theorem inner_le_of_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) {S : Set ℝ} {b : ℝ}
    (hb : ∀ i, hA.eigenvalues hn i ∈ S → hA.eigenvalues hn i ≤ b) {x : E}
    (hx : x ∈ hA.spectralSubspace hn S) : ⟪A x, x⟫ ≤ b * ‖x‖ ^ 2 := by
  rw [inner_eq_sum_eigen hA hn, norm_sq_eq_sum (hA.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hA.eigenvalues hn i ∈ S
  · exact mul_le_mul_of_nonneg_right (hb i hi) (sq_nonneg _)
  · have h0 := hA.eigenvectorBasis_repr_eq_zero_of_mem_spectralSubspace hn hi hx
    rw [OrthonormalBasis.repr_apply_apply] at h0
    simp [h0]

/-- Spectral projection of an arbitrary eigenvector: kept if its eigenvalue is selected. -/
theorem spectralProjection_of_eigen_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {S : Set ℝ} {μ : ℝ} (hμ : μ ∈ S) {w : E} (hw : A w = μ • w) :
    hA.spectralProjection hn S w = w := by
  simp only [LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.2 (mem_spectralSubspace_of_eigen hA hn hμ hw)

/-- ... and killed if it is not. -/
theorem spectralProjection_of_eigen_not_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {S : Set ℝ} {μ : ℝ} (hμ : μ ∉ S) {w : E} (hw : A w = μ • w) :
    hA.spectralProjection hn S w = 0 := by
  simp only [LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_apply_eq_zero_iff, ← spectralSubspace_compl hA hn S]
  exact mem_spectralSubspace_of_eigen hA hn (Set.mem_compl hμ) hw

/-- At most `count` orthonormal vectors lie in a spectral subspace. -/
theorem card_le_count (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) (S : Set ℝ) {k : ℕ}
    {v : Fin k → E} (hv : Orthonormal ℝ v) (hmem : ∀ j, v j ∈ hA.spectralSubspace hn S) :
    k ≤ countIn hA hn S := by
  rw [← finrank_spectralSubspace]
  let w : Fin k → hA.spectralSubspace hn S := fun j => ⟨v j, hmem j⟩
  have hw : LinearIndependent ℝ w :=
    LinearIndependent.of_comp (hA.spectralSubspace hn S).subtype hv.linearIndependent
  simpa using hw.fintype_card_le_finrank

end Spectral

section Split

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {p : ℕ} (hF : Module.finrank ℝ F = p)

/-- **Weyl split.** Every eigenvalue of `C Cᵀ` is `≤ h` or `≥ s2 - h`. -/
theorem eigen_split {C W : E →ₗ[ℝ] F} {s2 h : ℝ}
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hh : opn (gramL C - gramL W) ≤ h) (i : Fin p) :
    (gramL_isSymmetric C).eigenvalues hF i ≤ h ∨
      s2 - h ≤ (gramL_isSymmetric C).eigenvalues hF i := by
  have hw := (gramL_isSymmetric C).abs_eigenvalues_sub_le_opNorm (gramL_isSymmetric W) hF i
  have hw' : |(gramL_isSymmetric C).eigenvalues hF i - (gramL_isSymmetric W).eigenvalues hF i|
      ≤ h := hw.trans hh
  rw [abs_le] at hw'
  by_cases hi : (gramL_isSymmetric W).eigenvalues hF i ∈ Set.Ici s2
  · right; have := Set.mem_Ici.1 hi; linarith
  · left; have := hWL i hi; linarith

/-- The number of eigenvalues `≥ τ` is the rank count, for `h < τ < s2 - h`. -/
theorem count_eq_of_close {C W : E →ₗ[ℝ] F} {s2 h τ : ℝ}
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hh : opn (gramL C - gramL W) ≤ h) (h1 : h < τ) (h2 : τ < s2 - h) :
    countIn (gramL_isSymmetric C) hF (Set.Ici τ) = countIn (gramL_isSymmetric W) hF (Set.Ici s2) := by
  classical
  unfold countIn
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  have hw := (gramL_isSymmetric C).abs_eigenvalues_sub_le_opNorm (gramL_isSymmetric W) hF i
  have hw' : |(gramL_isSymmetric C).eigenvalues hF i - (gramL_isSymmetric W).eigenvalues hF i|
      ≤ h := hw.trans hh
  rw [abs_le] at hw'
  simp only [Set.mem_Ici]
  constructor
  · intro hC
    by_contra hW
    have := hWL i (by simpa using hW)
    linarith
  · intro hW; linarith

/-- **Eigenvalue split for any eigenvector.** -/
theorem eigenvalue_split {C W : E →ₗ[ℝ] F} {s2 h τ μ : ℝ}
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hh : opn (gramL C - gramL W) ≤ h) (h1 : h < τ) (h2 : τ < s2 - h)
    {u : F} (hu : u ≠ 0) (hμ : gramL C u = μ • u) :
    (τ ≤ μ → s2 - h ≤ μ) ∧ (μ < τ → μ ≤ h) := by
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hAu : ⟪gramL C u, u⟫ = μ * ‖u‖ ^ 2 := by
    rw [hμ, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor
  · intro hτμ
    have hmem := mem_spectralSubspace_of_eigen (gramL_isSymmetric C) hF
      (Set.mem_Ici.2 hτμ) hμ
    have := le_inner_of_mem' (gramL_isSymmetric C) hF (a := s2 - h) (fun i hi => by
      rcases eigen_split hF hWL hh i with h' | h'
      · exact absurd (lt_of_le_of_lt h' h1) (not_lt.2 (Set.mem_Ici.1 hi))
      · exact h') hmem
    rw [hAu] at this
    exact le_of_mul_le_mul_right this hpos
  · intro hμτ
    have hmem := mem_spectralSubspace_of_eigen (gramL_isSymmetric C) hF
      (S := (Set.Ici τ)ᶜ) (by simpa using hμτ) hμ
    have := inner_le_of_mem (gramL_isSymmetric C) hF (b := h) (fun i hi => by
      rcases eigen_split hF hWL hh i with h' | h'
      · exact h'
      · have : (gramL_isSymmetric C).eigenvalues hF i < τ := by simpa using hi
        linarith) hmem
    rw [hAu] at this
    exact le_of_mul_le_mul_right this hpos

end Split

end OpenTheory.TruncationEvent
