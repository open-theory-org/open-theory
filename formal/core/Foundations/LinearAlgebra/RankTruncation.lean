import SLT.MatrixInfra.Perturb

/-!
# Rank truncation: spectral projections and intertwining

For a linear map `C : E → F` between finite-dimensional real inner product spaces,
the Gram maps `C Cᵀ` (on `F`) and `Cᵀ C` (on `E`) are symmetric. Their spectral
projections onto eigenvalues in a set `S` (from the vendored SLT library) satisfy

  `P_S(C Cᵀ) ∘ C = C ∘ P_S(Cᵀ C)`   (`projL_comp`),

because `C` maps eigenvectors of `Cᵀ C` to eigenvectors of `C Cᵀ` with the same
eigenvalue. With `S = [τ, ∞)` the map `P_S(C Cᵀ) ∘ C` keeps exactly the singular
directions with `σ² ≥ τ`: it is the rank truncation used for the gradient-descent
plateau, and it equals `C ∘ P_S(Cᵀ C)`.
-/

noncomputable section
open LinearMap Submodule

namespace OpenTheory.RankTruncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Spectral subspaces of a symmetric map -/

section Spectral

variable {A : E →ₗ[ℝ] E} {n : ℕ}

/-- An eigenvector with eigenvalue in `S` lies in the spectral subspace of `S`. -/
theorem mem_spectralSubspace_of_eigen (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {S : Set ℝ} {μ : ℝ} (hμ : μ ∈ S) {w : E} (hw : A w = μ • w) :
    w ∈ hA.spectralSubspace hn S := by
  apply hA.mem_spectralSubspace_of_eigenvectorBasis_repr_eq_zero hn
  intro j hj
  rw [OrthonormalBasis.repr_apply_apply]
  have hne : hA.eigenvalues hn j ≠ μ := fun h => hj (h ▸ hμ)
  have key : hA.eigenvalues hn j * inner ℝ (hA.eigenvectorBasis hn j) w =
      μ * inner ℝ (hA.eigenvectorBasis hn j) w := by
    have h1 : inner ℝ (A (hA.eigenvectorBasis hn j)) w = inner ℝ (hA.eigenvectorBasis hn j) (A w) :=
      hA _ _
    rw [hA.apply_eigenvectorBasis hn j, hw, inner_smul_left, inner_smul_right] at h1
    simpa using h1
  have : (hA.eigenvalues hn j - μ) * inner ℝ (hA.eigenvectorBasis hn j) w = 0 := by
    rw [sub_mul]; linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

/-- The spectral subspace of the complement is the orthogonal complement. -/
theorem spectralSubspace_compl (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) (S : Set ℝ) :
    hA.spectralSubspace hn Sᶜ = (hA.spectralSubspace hn S)ᗮ := by
  apply le_antisymm
  · rw [LinearMap.IsSymmetric.spectralSubspace, Submodule.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal']
    intro u hu
    have h := hA.eigenvectorBasis_repr_eq_zero_of_mem_spectralSubspace hn hi hu
    rw [OrthonormalBasis.repr_apply_apply] at h
    dsimp only
    simpa [real_inner_comm] using h
  · intro x hx
    apply hA.mem_spectralSubspace_of_eigenvectorBasis_repr_eq_zero hn
    intro j hj
    rw [OrthonormalBasis.repr_apply_apply]
    have hmem : hA.eigenvectorBasis hn j ∈ hA.spectralSubspace hn S :=
      hA.eigenvectorBasis_mem_spectralSubspace hn (not_not.1 hj)
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).1 hx _ hmem

/-- Complementary spectral projections sum to the identity. -/
theorem spectralProjection_add_compl (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (S : Set ℝ) (x : E) :
    hA.spectralProjection hn S x + hA.spectralProjection hn Sᶜ x = x := by
  simp only [LinearMap.IsSymmetric.spectralProjection, spectralSubspace_compl hA hn S,
    ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_add_starProjection_orthogonal x

end Spectral

/-! ### Gram maps and intertwining -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `C Cᵀ`, on the output space. -/
def gramL (C : E →ₗ[ℝ] F) : F →ₗ[ℝ] F := C ∘ₗ LinearMap.adjoint C

/-- `Cᵀ C`, on the input space. -/
def gramR (C : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := LinearMap.adjoint C ∘ₗ C

theorem gramL_isSymmetric (C : E →ₗ[ℝ] F) : (gramL C).IsSymmetric := fun x y => by
  simp only [gramL, LinearMap.comp_apply]
  rw [← LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right]

theorem gramR_isSymmetric (C : E →ₗ[ℝ] F) : (gramR C).IsSymmetric := fun x y => by
  simp only [gramR, LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)

/-- Spectral projection of `C Cᵀ` onto eigenvalues in `S`. -/
def projL (C : E →ₗ[ℝ] F) (S : Set ℝ) : F →ₗ[ℝ] F := (gramL_isSymmetric C).spectralProjection hF S

/-- Spectral projection of `Cᵀ C` onto eigenvalues in `S`. -/
def projR (C : E →ₗ[ℝ] F) (S : Set ℝ) : E →ₗ[ℝ] E := (gramR_isSymmetric C).spectralProjection hE S

/-- `C` maps the spectral subspace of `Cᵀ C` for `S` into that of `C Cᵀ`. -/
theorem map_spectralSubspace (C : E →ₗ[ℝ] F) (S : Set ℝ) {x : E}
    (hx : x ∈ (gramR_isSymmetric C).spectralSubspace hE S) :
    C x ∈ (gramL_isSymmetric C).spectralSubspace hF S := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy
    apply mem_spectralSubspace_of_eigen _ hF hi
    set e := (gramR_isSymmetric C).eigenvectorBasis hE i
    have h : LinearMap.adjoint C (C e) =
        ((gramR_isSymmetric C).eigenvalues hE i : ℝ) • e := by
      have := (gramR_isSymmetric C).apply_eigenvectorBasis hE i
      rw [RCLike.ofReal_real_eq_id, id_eq] at this
      exact this
    dsimp only
    show C (LinearMap.adjoint C (C e)) = _
    rw [h, map_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- **Intertwining**: `P_S(C Cᵀ) ∘ C = C ∘ P_S(Cᵀ C)`. -/
theorem projL_comp (C : E →ₗ[ℝ] F) (S : Set ℝ) :
    projL hF C S ∘ₗ C = C ∘ₗ projR hE C S := by
  ext x
  simp only [LinearMap.comp_apply]
  have hsplit := spectralProjection_add_compl (gramR_isSymmetric C) hE S x
  have h1 : C (projR hE C S x) ∈ (gramL_isSymmetric C).spectralSubspace hF S :=
    map_spectralSubspace hE hF C S ((gramR_isSymmetric C).spectralProjection_apply_mem hE S x)
  have h2 : C ((gramR_isSymmetric C).spectralProjection hE Sᶜ x) ∈
      ((gramL_isSymmetric C).spectralSubspace hF S)ᗮ := by
    rw [← spectralSubspace_compl]
    exact map_spectralSubspace hE hF C Sᶜ ((gramR_isSymmetric C).spectralProjection_apply_mem hE Sᶜ x)
  conv_lhs => rw [← hsplit, map_add, map_add]
  rw [show projL hF C S (C ((gramR_isSymmetric C).spectralProjection hE S x)) =
      C ((gramR_isSymmetric C).spectralProjection hE S x) from
    (gramL_isSymmetric C).spectralProjection_eq_self_iff hF S |>.2 h1]
  have h0 : projL hF C S (C ((gramR_isSymmetric C).spectralProjection hE Sᶜ x)) = 0 := by
    simp only [projL, LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
    exact (Submodule.starProjection_apply_eq_zero_iff _).2 h2
  rw [h0, add_zero]
  rfl

end OpenTheory.RankTruncation
