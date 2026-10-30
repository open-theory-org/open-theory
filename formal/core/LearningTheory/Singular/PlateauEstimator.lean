import LearningTheory.Singular.PlateauFlow
import LearningTheory.Singular.TruncationEvent

/-!
# The gradient-descent plateau is the truncated SVD

Data `C : N × M` with an SVD `Uᵀ C V = diagData σ` (`U`, `V` orthogonal). The columns
`uₖ` of `U` are eigenvectors of `C Cᵀ` with eigenvalue `σₖ²` (`0` beyond `M`), so the
spectral projection of `C Cᵀ` onto `[τ, ∞)` keeps exactly the columns with `σₖ² ≥ τ`
(`proj_col`), and

  `trunc τ C = U · diagData (σ 1[σ² ≥ τ]) · Vᵀ`          (`trunc_eq_svd`).

Rotating `flow_plateau` by `(U, V)` then shows that on the good event
(`‖C Cᵀ - W Wᵀ‖ ≤ s2/4`), gradient flow from the aligned initialization reaches, at time
`√(2/s2) · log(1/ε)` and as `ε → 0`, exactly `trunc (s2/2) C` (`plateau_eq_trunc`).
-/

noncomputable section
open Set Real Filter Topology Matrix
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRisk OpenTheory.TruncationRank OpenTheory.TruncationEvent

namespace OpenTheory.Plateau

variable {M N H : ℕ}

local notation "EM" => EuclideanSpace ℝ (Fin M)
local notation "EN" => EuclideanSpace ℝ (Fin N)

/-! ### Matrix facts -/

theorem transpose_mul_self_of_mul_transpose {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (hU : U * Uᵀ = 1) : Uᵀ * U = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin k) (Fin k) ℝ rfl).mp hU

theorem eq_svd {C : Matrix (Fin N) (Fin M) ℝ} {U : Matrix (Fin N) (Fin N) ℝ}
    {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (hsvd : Uᵀ * C * V = diagData σ) : C = U * (diagData σ : Matrix (Fin N) (Fin M) ℝ) * Vᵀ := by
  rw [← hsvd]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hV, Matrix.mul_one]

/-- The squared singular values on the output side. -/
def ev (σ : ℕ → ℝ) (k : Fin N) : ℝ := if (k : ℕ) < M then σ k ^ 2 else 0

theorem diagData_mul_transpose (σ : ℕ → ℝ) :
    (diagData σ : Matrix (Fin N) (Fin M) ℝ) * (diagData σ)ᵀ = Matrix.diagonal (ev (M := M) σ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, diagData, Matrix.diagonal_apply, ev]
  by_cases hi : (i : ℕ) < M
  · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin M)]
    · by_cases hij : i = j
      · subst hij; simp [hi, sq]
      · have : (j : ℕ) ≠ i := fun h => hij (Fin.ext h.symm)
        simp [hij, this]
    · intro l _ hl
      have : (i : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero]
    · by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
    · intro l _
      have : (i : ℕ) ≠ l := fun h => hi (h ▸ l.2)
      simp [this]

/-- Column `k` of `U`. -/
def col (U : Matrix (Fin N) (Fin N) ℝ) (k : Fin N) : EN := toEuclideanLin U (EuclideanSpace.single k 1)

theorem inner_col {U : Matrix (Fin N) (Fin N) ℝ} (hU : U * Uᵀ = 1) (a b : Fin N) :
    ⟪col U a, col U b⟫ = if a = b then 1 else 0 := by
  have h := congrFun (congrFun (transpose_mul_self_of_mul_transpose hU) a) b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  rw [← h]
  simp [col, PiLp.inner_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem orthonormal_col {U : Matrix (Fin N) (Fin N) ℝ} (hU : U * Uᵀ = 1) :
    Orthonormal ℝ (col U) := by
  classical
  rw [orthonormal_iff_ite]; exact inner_col hU

theorem gramL_toEuclideanLin (C : Matrix (Fin N) (Fin M) ℝ) :
    gramL (toEuclideanLin C) = toEuclideanLin (C * Cᵀ) := by
  rw [gramL, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.toLpLin_mul]

/-- Columns of `U` are eigenvectors of `C Cᵀ`. -/
theorem gramL_col {C : Matrix (Fin N) (Fin M) ℝ} {U : Matrix (Fin N) (Fin N) ℝ}
    {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (hsvd : Uᵀ * C * V = diagData σ) (k : Fin N) :
    gramL (toEuclideanLin C) (col U k) = ev (M := M) σ k • col U k := by
  have hC := eq_svd hU hV hsvd
  have hVV := transpose_mul_self_of_mul_transpose hV
  have hUU := transpose_mul_self_of_mul_transpose hU
  have key : C * Cᵀ * U = U * Matrix.diagonal (ev (M := M) σ) := by
    rw [← diagData_mul_transpose, hC]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, hVV, Matrix.one_mul, hUU, Matrix.mul_one]
  rw [gramL_toEuclideanLin, col, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul, key,
    Matrix.toLpLin_mul, LinearMap.comp_apply, ← map_smul]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

/-! ### The truncated SVD in SVD coordinates -/

theorem finrank_EN : Module.finrank ℝ EN = N := finrank_euclideanSpace_fin
theorem finrank_EM : Module.finrank ℝ EM = M := finrank_euclideanSpace_fin

/-- The spectral projection keeps exactly the columns with `σₖ² ≥ τ`. -/
theorem proj_col {C : Matrix (Fin N) (Fin M) ℝ} {U : Matrix (Fin N) (Fin N) ℝ}
    {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (hsvd : Uᵀ * C * V = diagData σ) (τ : ℝ) (k : Fin N) :
    Ptop finrank_EN (toEuclideanLin C) τ (col U k) =
      if τ ≤ ev (M := M) σ k then col U k else 0 := by
  have hk := gramL_col hU hV hsvd k
  split_ifs with h
  · exact spectralProjection_of_eigen_mem (gramL_isSymmetric _) finrank_EN (Set.mem_Ici.2 h) hk
  · exact spectralProjection_of_eigen_not_mem (gramL_isSymmetric _) finrank_EN
      (fun h' => h (Set.mem_Ici.1 h')) hk

/-- Singular values kept by the threshold `τ`. -/
def keep (σ : ℕ → ℝ) (τ : ℝ) (k : ℕ) : ℝ := if τ ≤ σ k ^ 2 then σ k else 0

/-- **The truncated SVD in SVD coordinates.** -/
theorem trunc_eq_svd {C : Matrix (Fin N) (Fin M) ℝ} {U : Matrix (Fin N) (Fin N) ℝ}
    {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (hsvd : Uᵀ * C * V = diagData σ) (τ : ℝ) :
    trunc finrank_EN (toEuclideanLin C) τ =
      toEuclideanLin (U * (diagData (keep σ τ) : Matrix (Fin N) (Fin M) ℝ) * Vᵀ) := by
  classical
  set δ : Fin N → ℝ := fun k => if τ ≤ ev (M := M) σ k then 1 else 0
  have hPU : Ptop finrank_EN (toEuclideanLin C) τ ∘ₗ toEuclideanLin U =
      toEuclideanLin (U * Matrix.diagonal δ) := by
    refine (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.ext fun k => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
    rw [show toEuclideanLin U (EuclideanSpace.single k 1) = col U k from rfl, proj_col hU hV hsvd,
      Matrix.toLpLin_mul, LinearMap.comp_apply]
    have : toEuclideanLin (Matrix.diagonal δ) (EuclideanSpace.single k 1) =
        δ k • EuclideanSpace.single k (1 : ℝ) := by
      ext i; simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
      split_ifs with h <;> simp [h]
    rw [this, map_smul]
    simp only [δ]; split_ifs <;> simp [col]
  have hD : Matrix.diagonal δ * (diagData σ : Matrix (Fin N) (Fin M) ℝ) = diagData (keep σ τ) := by
    ext i j
    simp only [Matrix.diagonal_mul, diagData, δ, keep, ev]
    by_cases hij : (i : ℕ) = j
    · have hi : (i : ℕ) < M := hij ▸ j.2
      simp [hij]
    · simp [hij]
  have hCfac : toEuclideanLin C = toEuclideanLin U ∘ₗ
      toEuclideanLin ((diagData σ : Matrix (Fin N) (Fin M) ℝ) * Vᵀ) := by
    rw [← Matrix.toLpLin_mul 2 2 2, ← Matrix.mul_assoc, ← eq_svd hU hV hsvd]
  calc trunc finrank_EN (toEuclideanLin C) τ
      = Ptop finrank_EN (toEuclideanLin C) τ ∘ₗ toEuclideanLin C := rfl
    _ = Ptop finrank_EN (toEuclideanLin C) τ ∘ₗ (toEuclideanLin U ∘ₗ
          toEuclideanLin ((diagData σ : Matrix (Fin N) (Fin M) ℝ) * Vᵀ)) := by
        nth_rw 2 [hCfac]
    _ = toEuclideanLin (U * Matrix.diagonal δ) ∘ₗ
          toEuclideanLin ((diagData σ : Matrix (Fin N) (Fin M) ℝ) * Vᵀ) := by
        rw [← LinearMap.comp_assoc, hPU]
    _ = toEuclideanLin (U * Matrix.diagonal δ * ((diagData σ : Matrix (Fin N) (Fin M) ℝ) * Vᵀ)) :=
        (Matrix.toLpLin_mul 2 2 2 _ _).symm
    _ = _ := by rw [← Matrix.mul_assoc, Matrix.mul_assoc U, hD]

/-! ### Rotating the plateau back -/

theorem of_prodBA (p : State M N H) :
    Matrix.of (prodBA p) = Matrix.of p.2 * Matrix.of p.1 := by
  ext i j; simp [prodBA, Matrix.mul_apply]

theorem abs_entry_le_one {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ} (hU : U * Uᵀ = 1) (i a : Fin k) :
    |U i a| ≤ 1 := by
  have h := congrFun (congrFun hU i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have : U i a * U i a ≤ 1 := h ▸ Finset.single_le_sum (f := fun l => U i l * U i l)
    (fun l _ => mul_self_nonneg _) (Finset.mem_univ a)
  exact abs_le_one_iff_mul_self_le_one.2 this

theorem abs_conj_entry_le {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) {D : Matrix (Fin N) (Fin M) ℝ} {δ : ℝ}
    (hD : ∀ a b, |D a b| ≤ δ) (i : Fin N) (j : Fin M) :
    |(U * D * Vᵀ) i j| ≤ N * M * δ := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc |∑ b, (∑ a, U i a * D a b) * V j b| ≤ ∑ b : Fin M, ∑ a : Fin N, δ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [abs_mul]
        refine (mul_le_mul_of_nonneg_left (abs_entry_le_one hV j b) (abs_nonneg _)).trans ?_
        rw [mul_one]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        rw [abs_mul]
        calc |U i a| * |D a b| ≤ 1 * δ :=
              mul_le_mul (abs_entry_le_one hU i a) (hD a b) (abs_nonneg _) zero_le_one
          _ = δ := one_mul δ
    _ = N * M * δ := by simp [Finset.sum_const]; ring

/-- `flow_plateau` for general data `C = U diag(σ) Vᵀ`, from the rotated aligned start. -/
theorem rotated_plateau_window (hHM : H ≤ M) (hHN : H ≤ N) {C : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ)
    {σmin : ℝ} (hmin : 0 < σmin) (hσ : ∀ i, σmin ≤ σ i) {c₁ c₂ : ℝ}
    (signal : Fin H → Prop) [DecidablePred signal]
    (hsig : ∀ k, signal k → 1 < σ k * c₁) (hnoise : ∀ k, ¬ signal k → σ k * c₂ < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H, (∀ t, HasDerivAt f (gradField C (f t)) t) →
      rotate U V (f 0) = initState ε → ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)),
        0 ≤ t → ∀ i j,
        |prodBA (f t) i j - (U * Matrix.of (fun (a : Fin N) (b : Fin M) =>
          if h : (a : ℕ) = b ∧ (a : ℕ) < H then (if signal ⟨a, h.2⟩ then σ a else 0) else 0) *
            Vᵀ) i j| < δ := by
  have hNM : (0 : ℝ) < N * M + 1 := by positivity
  set δ' := δ / (N * M + 1)
  have hδ' : 0 < δ' := div_pos hδ hNM
  filter_upwards [flow_plateau hHM hHN hmin hσ signal hsig hnoise hδ'] with
    ε hε f hf h0 t ht ht0 i j
  let g : ℝ → State M N H := fun s => rotate U V (f s)
  have hg : ∀ s, HasDerivAt g (gradField (diagData σ) (g s)) s := fun s => by
    have := rotate_solves hU hV C (hf s); rwa [hsvd] at this
  have hG := hε t g (fun s _ => (hg s).continuousAt.continuousWithinAt)
    (fun s _ => (hg s).hasDerivWithinAt) h0 t ht ht0 le_rfl
  set L : Matrix (Fin N) (Fin M) ℝ := Matrix.of (fun (a : Fin N) (b : Fin M) =>
    if h : (a : ℕ) = b ∧ (a : ℕ) < H then (if signal ⟨a, h.2⟩ then σ a else 0) else 0)
  have hP : Matrix.of (prodBA (f t)) = U * Matrix.of (prodBA (g t)) * Vᵀ := by
    have hUU := transpose_mul_self_of_mul_transpose hU
    have hVV := hV
    rw [of_prodBA, of_prodBA]
    show _ = U * ((Uᵀ * Matrix.of (f t).2) * (Matrix.of (f t).1 * V)) * Vᵀ
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc _ V, hVV, Matrix.mul_one]
  have hdiff : Matrix.of (prodBA (f t)) - U * L * Vᵀ = U * (Matrix.of (prodBA (g t)) - L) * Vᵀ := by
    rw [hP, Matrix.mul_sub, Matrix.sub_mul]
  have hb := abs_conj_entry_le hU hV (D := Matrix.of (prodBA (g t)) - L) (δ := δ')
    (fun a b => (hG a b).le) i j
  rw [← hdiff] at hb
  calc |prodBA (f t) i j - (U * L * Vᵀ) i j| ≤ N * M * δ' := hb
    _ < δ := by
      rw [show (N : ℝ) * M * δ' = δ * ((N * M) / (N * M + 1)) by simp only [δ']; ring]
      exact mul_lt_of_lt_one_right hδ ((div_lt_one hNM).2 (by linarith))

/-- `rotated_plateau_window` at the single time `c log (1/ε)`. -/
theorem rotated_plateau (hHM : H ≤ M) (hHN : H ≤ N) {C : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ)
    {σmin : ℝ} (hmin : 0 < σmin) (hσ : ∀ i, σmin ≤ σ i) {c : ℝ}
    (signal : Fin H → Prop) [DecidablePred signal]
    (hsig : ∀ k, signal k → 1 < σ k * c) (hnoise : ∀ k, ¬ signal k → σ k * c < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H, (∀ t, HasDerivAt f (gradField C (f t)) t) →
      rotate U V (f 0) = initState ε → 0 ≤ c * log (1 / ε) → ∀ i j,
        |prodBA (f (c * log (1 / ε))) i j - (U * Matrix.of (fun (a : Fin N) (b : Fin M) =>
          if h : (a : ℕ) = b ∧ (a : ℕ) < H then (if signal ⟨a, h.2⟩ then σ a else 0) else 0) *
            Vᵀ) i j| < δ := by
  filter_upwards [rotated_plateau_window hHM hHN hU hV hsvd hmin hσ signal hsig hnoise hδ] with
    ε hε f hf h0 ht0 i j
  exact hε f hf h0 _ ⟨le_rfl, le_rfl⟩ ht0 i j

/-! ### On the good event, the plateau is the truncated SVD -/

/-- No singular value at index `≥ H` passes the threshold: otherwise `k + 1 > r`
orthonormal columns would fit in the `r`-dimensional spectral subspace. -/
theorem sq_lt_of_ge {C W : Matrix (Fin N) (Fin M) ℝ} {U : Matrix (Fin N) (Fin N) ℝ}
    {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ} (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1)
    (hsvd : Uᵀ * C * V = diagData σ) (hanti : Antitone σ) (hpos : ∀ k, 0 < σ k) {s2 : ℝ}
    (hs2 : 0 < s2)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i = 0)
    (hclose : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ s2 / 4)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W)) finrank_EN (Set.Ici s2) ≤ H)
    {k : ℕ} (hkN : k < N) (hkM : k < M) (hHk : H ≤ k) : σ k ^ 2 < s2 / 2 := by
  by_contra hk
  replace hk := not_lt.1 hk
  let v : Fin (k + 1) → EN := fun j => col U ⟨j, by omega⟩
  have hv : Orthonormal ℝ v :=
    (orthonormal_col hU).comp _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  have hmem : ∀ j, v j ∈ (gramL_isSymmetric (toEuclideanLin C)).spectralSubspace finrank_EN
      (Set.Ici (s2 / 2)) := by
    intro j
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.2
    have hev : ev (M := M) σ (⟨j, by omega⟩ : Fin N) = σ j ^ 2 := by
      simp [ev, show (j : ℕ) < M by omega]
    refine mem_spectralSubspace_of_eigen _ finrank_EN (μ := σ j ^ 2) ?_ ?_
    · exact Set.mem_Ici.2 (hk.trans (pow_le_pow_left₀ (hpos k).le (hanti hjk) 2))
    · have := gramL_col hU hV hsvd (⟨j, by omega⟩ : Fin N); rwa [hev] at this
  have hcard := card_le_count _ finrank_EN _ hv hmem
  rw [count_eq_of_close finrank_EN hWL hclose (by linarith) (by linarith)] at hcard
  omega

/-- The plateau matrix, with signal `σₖ² ≥ s2/2`, is the kept part of `diag σ`. -/
theorem plateauMatrix_eq {C W : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ) (hanti : Antitone σ)
    (hpos : ∀ k, 0 < σ k) {s2 : ℝ} (hs2 : 0 < s2)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i = 0)
    (hclose : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ s2 / 4)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W)) finrank_EN (Set.Ici s2) ≤ H) :
    (Matrix.of (fun (a : Fin N) (b : Fin M) =>
      if h : (a : ℕ) = b ∧ (a : ℕ) < H then
        (if s2 / 2 ≤ σ ((⟨a, h.2⟩ : Fin H) : ℕ) ^ 2 then σ a else 0) else 0)) =
      (diagData (keep σ (s2 / 2)) : Matrix (Fin N) (Fin M) ℝ) := by
  ext a b
  simp only [Matrix.of_apply]
  unfold diagData
  by_cases hab : (a : ℕ) = b
  · rw [ite_eq_left hab]
    by_cases haH : (a : ℕ) < H
    · rw [dite_eq_left ⟨hab, haH⟩]; rfl
    · rw [dite_eq_right (fun h => haH h.2)]
      have hlt := sq_lt_of_ge hU hV hsvd hanti hpos hs2 hWL hclose hrH a.2 (hab ▸ b.2)
        (not_lt.1 haH)
      simp only [keep, ite_eq_right (not_le.2 hlt)]
  · rw [dite_eq_right (fun h => hab h.1), ite_eq_right hab]

/-- **The gradient-descent plateau is the truncated SVD.** On the good event
`‖C Cᵀ - W Wᵀ‖ ≤ s2/4`, with `rank W ≤ H ≤ min(M, N)` and an SVD of `C` with positive,
decreasing singular values, gradient flow from the aligned start reaches, at time
`√(2/s2) log(1/ε)` and as `ε → 0`, the hard-thresholded SVD `trunc (s2/2) C`. -/
theorem plateau_eq_trunc (hHM : H ≤ M) (hHN : H ≤ N) {C W : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ)
    (hanti : Antitone σ) {σmin : ℝ} (hmin : 0 < σmin) (hσ : ∀ k, σmin ≤ σ k) {s2 : ℝ}
    (hs2 : 0 < s2)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i = 0)
    (hclose : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ s2 / 4)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W)) finrank_EN (Set.Ici s2) ≤ H)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H, (∀ t, HasDerivAt f (gradField C (f t)) t) →
      rotate U V (f 0) = initState ε → ∀ i j,
        |prodBA (f (√(2 / s2) * log (1 / ε))) i j -
          toEuclideanLin.symm (trunc finrank_EN (toEuclideanLin C) (s2 / 2)) i j| < δ := by
  have hpos : ∀ k, 0 < σ k := fun k => hmin.trans_le (hσ k)
  set c := √(2 / s2)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 2 / s2 := Real.sq_sqrt (by positivity)
  let signal : Fin H → Prop := fun k => s2 / 2 ≤ σ k ^ 2
  -- eigenvalue split for the first `H` columns
  have split : ∀ k : Fin H, (s2 / 2 ≤ σ k ^ 2 → s2 - s2 / 4 ≤ σ k ^ 2) ∧
      (σ k ^ 2 < s2 / 2 → σ k ^ 2 ≤ s2 / 4) := by
    intro k
    have hkM : (k : ℕ) < M := lt_of_lt_of_le k.2 hHM
    have hkN : (k : ℕ) < N := lt_of_lt_of_le k.2 hHN
    have hev : ev (M := M) σ (⟨k, hkN⟩ : Fin N) = σ k ^ 2 := by simp [ev, hkM]
    have heig := gramL_col hU hV hsvd (⟨k, hkN⟩ : Fin N)
    rw [hev] at heig
    exact eigenvalue_split finrank_EN hWL hclose (by linarith) (by linarith)
      ((orthonormal_col hU).ne_zero _) heig
  have hsig : ∀ k, signal k → 1 < σ k * c := by
    intro k hk
    have h1 := (split k).1 hk
    have hsq : (1 : ℝ) ^ 2 < (σ k * c) ^ 2 := by
      rw [mul_pow, hc2, one_pow]
      have : σ k ^ 2 * (2 / s2) ≥ (3 * s2 / 4) * (2 / s2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e : (3 * s2 / 4) * (2 / s2) = 3 / 2 := by field_simp; ring
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (mul_pos (hpos k) hc).le hsq
  have hnoise : ∀ k, ¬ signal k → σ k * c < 1 := by
    intro k hk
    have h1 := (split k).2 (lt_of_not_ge hk)
    have hsq : (σ k * c) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [mul_pow, hc2, one_pow]
      have : σ k ^ 2 * (2 / s2) ≤ (s2 / 4) * (2 / s2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have e : (s2 / 4) * (2 / s2) = 1 / 2 := by field_simp; ring
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hsq
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε using hε.2
  have hpos' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [rotated_plateau hHM hHN hU hV hsvd hmin hσ signal hsig hnoise hδ, hsmall, hpos']
    with ε hε hε1 hε0 f hf h0 i j
  have ht0 : 0 ≤ c * log (1 / ε) :=
    mul_nonneg hc.le (Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith))
  have key := hε f hf h0 ht0 i j
  -- the plateau matrix is `U diagData (keep σ (s2/2)) Vᵀ`
  have hL : (Matrix.of (fun (a : Fin N) (b : Fin M) =>
      if h : (a : ℕ) = b ∧ (a : ℕ) < H then (if signal ⟨a, h.2⟩ then σ a else 0) else 0)) =
      (diagData (keep σ (s2 / 2)) : Matrix (Fin N) (Fin M) ℝ) :=
    plateauMatrix_eq hU hV hsvd hanti hpos hs2 hWL hclose hrH
  rw [hL] at key
  rw [trunc_eq_svd hU hV hsvd, LinearEquiv.symm_apply_apply]
  exact key

end OpenTheory.Plateau
