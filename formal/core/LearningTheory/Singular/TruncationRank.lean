import LearningTheory.Singular.TruncationRisk

/-!
# The limit risk equals `r (M + N - r)`

Specializes `tendsto_risk` to i.i.d. `N(0,1)` matrix entries: the noise space is
`EuclideanSpace ℝ (κ × ι)` and `noiseOp x = Σ x(k,l) bF_k ⊗ bE_l`. Then

  `Σₐ ‖P_T(Φ gₐ)‖²_HS = N M - (N - r)(M - r) = r (M + N - r)`,

the dimension of the manifold of rank-`r` `N × M` matrices, where `r` is the number of
eigenvalues `≥ s2` of `W Wᵀ`, which equals the number for `Wᵀ W` (`rankL_eq_rankR`).
Main result: `tendsto_risk_iid`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRisk

namespace OpenTheory.TruncationRank

/-! ### Counting eigenvalues -/

section Count

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →ₗ[ℝ] E} {n : ℕ}

open Classical in
/-- The number of eigenvalues of `A` in `S`. -/
def countIn (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) (S : Set ℝ) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues hn i ∈ S).card

theorem spectralProjection_eigen_of_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {S : Set ℝ} {i : Fin n} (hi : hA.eigenvalues hn i ∈ S) :
    hA.spectralProjection hn S (hA.eigenvectorBasis hn i) = hA.eigenvectorBasis hn i := by
  simp only [LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.2 (hA.eigenvectorBasis_mem_spectralSubspace hn hi)

theorem spectralProjection_eigen_of_not_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {S : Set ℝ} {i : Fin n} (hi : hA.eigenvalues hn i ∉ S) :
    hA.spectralProjection hn S (hA.eigenvectorBasis hn i) = 0 := by
  simp only [LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  rw [Submodule.starProjection_apply_eq_zero_iff, ← spectralSubspace_compl hA hn S]
  exact hA.eigenvectorBasis_mem_spectralSubspace hn hi

/-- The Hilbert–Schmidt mass of a spectral projection is the number of selected eigenvalues,
in any orthonormal basis. -/
theorem sum_norm_sq_spectralProjection (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (S : Set ℝ) {κ : Type*} [Fintype κ] (c : OrthonormalBasis κ ℝ E) :
    ∑ k, ‖hA.spectralProjection hn S (c k)‖ ^ 2 = countIn hA hn S := by
  classical
  have hsym := spectralProjection_isSymmetric hA hn S
  rw [← hs_sq, hs_sq_adjoint c (hA.eigenvectorBasis hn), hsym.adjoint_eq, hs_sq, countIn,
    Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : hA.eigenvalues hn i ∈ S
  · rw [spectralProjection_eigen_of_mem hA hn hi, (hA.eigenvectorBasis hn).norm_eq_one]; simp [hi]
  · rw [spectralProjection_eigen_of_not_mem hA hn hi]; simp [hi]

theorem countIn_compl (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) (S : Set ℝ) :
    (countIn hA hn Sᶜ : ℝ) = n - countIn hA hn S := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => hA.eigenvalues hn i ∈ S)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [countIn, countIn, eq_sub_iff_add_eq, ← Nat.cast_add, add_comm]
  simp only [Set.mem_compl_iff]
  exact_mod_cast h

/-- `finrank` of a spectral subspace is the eigenvalue count. -/
theorem finrank_spectralSubspace (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (S : Set ℝ) : Module.finrank ℝ (hA.spectralSubspace hn S) = countIn hA hn S := by
  classical
  rw [LinearMap.IsSymmetric.spectralSubspace, finrank_span_eq_card, countIn,
    Fintype.card_subtype]
  exact (hA.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective

/-- On the spectral subspace of `[s, ∞)`, `⟪A x, x⟫ ≥ s ‖x‖²`. -/
theorem le_inner_of_mem (hA : A.IsSymmetric) (hn : Module.finrank ℝ E = n) {s : ℝ} {x : E}
    (hx : x ∈ hA.spectralSubspace hn (Set.Ici s)) : s * ‖x‖ ^ 2 ≤ ⟪A x, x⟫ := by
  set v := hA.eigenvectorBasis hn
  have hAx : ⟪A x, x⟫ = ∑ i, hA.eigenvalues hn i * ⟪v i, x⟫ ^ 2 := by
    rw [← v.sum_inner_mul_inner (A x) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ⟪A x, v i⟫ = hA.eigenvalues hn i * ⟪v i, x⟫ := by
      rw [hA x (v i), hA.apply_eigenvectorBasis hn i, RCLike.ofReal_real_eq_id, id_eq,
        real_inner_smul_right, real_inner_comm]
    rw [h1]; ring
  rw [hAx, norm_sq_eq_sum v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hA.eigenvalues hn i ∈ Set.Ici s
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · have h0 := hA.eigenvectorBasis_repr_eq_zero_of_mem_spectralSubspace hn hi hx
    rw [OrthonormalBasis.repr_apply_apply] at h0
    simp [v, h0]

end Count

/-! ### `rank` from the left and from the right agree -/

section Rank

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)

/-- `Cᵀ` maps the spectral subspace of `C Cᵀ` for `S` into that of `Cᵀ C`. -/
theorem map_spectralSubspace_adjoint (C : E →ₗ[ℝ] F) (S : Set ℝ) {y : F}
    (hy : y ∈ (gramL_isSymmetric C).spectralSubspace hF S) :
    LinearMap.adjoint C y ∈ (gramR_isSymmetric C).spectralSubspace hE S := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hz
    apply mem_spectralSubspace_of_eigen _ hE hi
    set e := (gramL_isSymmetric C).eigenvectorBasis hF i
    have h : C (LinearMap.adjoint C e) = ((gramL_isSymmetric C).eigenvalues hF i : ℝ) • e := by
      have := (gramL_isSymmetric C).apply_eigenvectorBasis hF i
      rw [RCLike.ofReal_real_eq_id, id_eq] at this
      exact this
    dsimp only
    show LinearMap.adjoint C (C (LinearMap.adjoint C e)) = _
    rw [h, map_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-- The number of squared singular values `≥ s` is the same from both sides. -/
theorem rankL_eq_rankR (C : E →ₗ[ℝ] F) {s : ℝ} (hs : 0 < s) :
    countIn (gramL_isSymmetric C) hF (Set.Ici s) = countIn (gramR_isSymmetric C) hE (Set.Ici s) := by
  rw [← finrank_spectralSubspace, ← finrank_spectralSubspace]
  set KL := (gramL_isSymmetric C).spectralSubspace hF (Set.Ici s)
  set KR := (gramR_isSymmetric C).spectralSubspace hE (Set.Ici s)
  apply le_antisymm
  · let f : KL →ₗ[ℝ] KR := (LinearMap.adjoint C).restrict
      (fun y hy => map_spectralSubspace_adjoint hE hF C _ hy)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun y y' hyy => ?_
    rw [← sub_eq_zero] at hyy ⊢
    rw [← map_sub] at hyy
    set z := y - y'
    have hz0 : LinearMap.adjoint C (z : F) = 0 := by
      have := congrArg Subtype.val hyy; simpa [f] using this
    have hle := le_inner_of_mem (gramL_isSymmetric C) hF z.2
    have : ⟪gramL C z, (z : F)⟫ = 0 := by
      simp only [gramL, LinearMap.comp_apply, hz0, map_zero, inner_zero_left]
    rw [this] at hle
    have : ‖(z : F)‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖(z : F)‖]) (sq_nonneg _)
    exact Subtype.ext (by simpa using this)
  · let f : KR →ₗ[ℝ] KL := C.restrict (fun x hx => map_spectralSubspace hE hF C _ hx)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x x' hxx => ?_
    rw [← sub_eq_zero] at hxx ⊢
    rw [← map_sub] at hxx
    set z := x - x'
    have hz0 : C (z : E) = 0 := by
      have := congrArg Subtype.val hxx; simpa [f] using this
    have hle := le_inner_of_mem (gramR_isSymmetric C) hE z.2
    have : ⟪gramR C z, (z : E)⟫ = 0 := by
      simp only [gramR, LinearMap.comp_apply, hz0, map_zero, inner_zero_left]
    rw [this] at hle
    have : ‖(z : E)‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖(z : E)‖]) (sq_nonneg _)
    exact Subtype.ext (by simpa using this)

end Rank

/-! ### Rank-one maps and the tangent projection -/

section RankOne

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The rank-one map `f eᵀ : y ↦ ⟪e, y⟫ f`. -/
def rk (f : F) (e : E) : E →ₗ[ℝ] F where
  toFun y := ⟪e, y⟫ • f
  map_add' y y' := by simp [inner_add_right, add_smul]
  map_smul' c y := by simp [real_inner_smul_right, smul_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hs_sq_rk_sub (b : OrthonormalBasis ι ℝ E) (u u' : F) (v v' : E) :
    hs b (rk u v - rk u' v') ^ 2 =
      ‖v‖ ^ 2 * ‖u‖ ^ 2 - 2 * (⟪v, v'⟫ * ⟪u, u'⟫) + ‖v'‖ ^ 2 * ‖u'‖ ^ 2 := by
  rw [hs_sq]
  simp only [LinearMap.sub_apply, rk, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1 : ∀ w : E, ∑ i, ⟪w, b i⟫ ^ 2 = ‖w‖ ^ 2 := fun w => by
    rw [norm_sq_eq_sum b]; simp_rw [real_inner_comm]
  have h2 : ∑ i, 2 * (⟪v, b i⟫ * (⟪v', b i⟫ * ⟪u, u'⟫)) = 2 * (⟪v, v'⟫ * ⟪u, u'⟫) := by
    rw [← b.sum_inner_mul_inner v v', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (b i) v']; ring
  rw [h1, h1, h2]

/-- Symmetric idempotents: `⟪u, P u⟫ = ‖P u‖²`. -/
theorem inner_self_proj {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {P : G →ₗ[ℝ] G} (hP : P.IsSymmetric) (hPP : ∀ y, P (P y) = P y) (u : G) :
    ⟪u, P u⟫ = ‖P u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hP u (P u), hPP]

theorem Qbot_idem (C : E →ₗ[ℝ] F) (τ : ℝ) (x : E) :
    Qbot hE C τ (Qbot hE C τ x) = Qbot hE C τ x := by
  simp only [Qbot, projR, LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)

theorem tangent_rk (W : E →ₗ[ℝ] F) (s2 : ℝ) (f : F) (e : E) :
    tangent hE hF W s2 (rk f e) = rk f e - rk (Pbot hF W s2 f) (Qbot hE W s2 e) := by
  have sQ : (Qbot hE W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric W) hE _
  ext y
  simp only [tangent, rk, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, map_smul, sQ e y]

/-- For unit `f, e`: `‖P_T(f eᵀ)‖² = 1 - ‖P⊥ f‖² ‖Q⊥ e‖²`. -/
theorem hs_sq_tangent_rk (b : OrthonormalBasis ι ℝ E) (W : E →ₗ[ℝ] F) (s2 : ℝ) {f : F} {e : E}
    (hf : ‖f‖ = 1) (he : ‖e‖ = 1) :
    hs b (tangent hE hF W s2 (rk f e)) ^ 2 =
      1 - ‖Pbot hF W s2 f‖ ^ 2 * ‖Qbot hE W s2 e‖ ^ 2 := by
  have sP : (Pbot hF W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramL_isSymmetric W) hF _
  have sQ : (Qbot hE W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric W) hE _
  rw [tangent_rk, hs_sq_rk_sub, inner_self_proj sP (Pbot_idem hF W s2),
    inner_self_proj sQ (Qbot_idem hE W s2), hf, he]
  ring

end RankOne

/-! ### i.i.d. Gaussian entries -/

section IID

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The noise matrix with entries `x (k, l)` in the bases `bF`, `bE`. -/
def noiseOp (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis κ ℝ F) :
    EuclideanSpace ℝ (κ × ι) →ₗ[ℝ] (E →ₗ[ℝ] F) where
  toFun x := ∑ a, x a • rk (bF a.1) (bE a.2)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem noiseOp_basisFun (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis κ ℝ F)
    (a : κ × ι) :
    noiseOp bE bF (EuclideanSpace.basisFun (κ × ι) ℝ a) = rk (bF a.1) (bE a.2) := by
  simp [noiseOp, EuclideanSpace.basisFun_apply, PiLp.single_apply]

/-- **The limit value**: `Σₐ ‖P_T(Φ gₐ)‖² = r (M + N - r)`, with `r` the number of squared
singular values `≥ s2`. -/
theorem sum_hs_sq_tangent_noise (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis κ ℝ F)
    (W : E →ₗ[ℝ] F) {s2 : ℝ} (hs2 : 0 < s2) :
    ∑ a, hs bE (tangent hE hF W s2 (noiseOp bE bF (EuclideanSpace.basisFun (κ × ι) ℝ a))) ^ 2 =
      (countIn (gramL_isSymmetric W) hF (Set.Ici s2) : ℝ) *
        (m + p - countIn (gramL_isSymmetric W) hF (Set.Ici s2)) := by
  simp_rw [noiseOp_basisFun]
  simp_rw [hs_sq_tangent_rk hE hF bE W s2 (bF.norm_eq_one _) (bE.norm_eq_one _)]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, ← Finset.sum_mul]
  have hP : ∑ k, ‖Pbot hF W s2 (bF k)‖ ^ 2 = p - countIn (gramL_isSymmetric W) hF (Set.Ici s2) := by
    rw [← countIn_compl]; exact sum_norm_sq_spectralProjection _ hF _ bF
  have hQ : ∑ l, ‖Qbot hE W s2 (bE l)‖ ^ 2 = m - countIn (gramL_isSymmetric W) hF (Set.Ici s2) := by
    rw [rankL_eq_rankR hE hF W hs2, ← countIn_compl]
    exact sum_norm_sq_spectralProjection _ hE _ bE
  have hκ : (Fintype.card κ : ℝ) = p := by
    rw [← hF, Module.finrank_eq_card_basis bF.toBasis]
  have hι : (Fintype.card ι : ℝ) = m := by
    rw [← hE, Module.finrank_eq_card_basis bE.toBasis]
  simp only [Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hP, hQ, hκ, hι]
  ring

/-- **Main theorem.** Truncated SVD under i.i.d. `N(0,1)` noise of size `n^{-1/2}`: if every
nonzero eigenvalue of `W Wᵀ` and `Wᵀ W` is `≥ s2` and `0 < τ < s2`, then

  `n · E ‖trunc τ (W + n^{-1/2} Z) - W‖²_F  →  r (M + N - r)`,

the dimension of the rank-`r` matrix manifold (`M = dim E`, `N = dim F`). -/
theorem tendsto_risk_iid (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis κ ℝ F)
    {W : E →ₗ[ℝ] F} {s2 τ : ℝ} (hτ : 0 < τ) (hτs : τ < s2)
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0) :
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal
        (n * hs bE (trunc hF (W + (Real.sqrt n)⁻¹ • noiseOp bE bF x) τ - W) ^ 2)
          ∂(stdGaussian (EuclideanSpace ℝ (κ × ι))))
      atTop (𝓝 (ENNReal.ofReal ((countIn (gramL_isSymmetric W) hF (Set.Ici s2) : ℝ) *
        (m + p - countIn (gramL_isSymmetric W) hF (Set.Ici s2))))) := by
  rw [← sum_hs_sq_tangent_noise hE hF bE bF W (hτ.trans hτs)]
  exact tendsto_risk hE hF bE (EuclideanSpace.basisFun (κ × ι) ℝ) (noiseOp bE bF) hτ hτs hWL hWR

end IID

end OpenTheory.TruncationRank
