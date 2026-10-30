import LearningTheory.Singular.BalancedFlow
import LearningTheory.Singular.StoppingRule

/-!
# The plateau from a balanced random initialization

Diagonal data `C = diagData σ`. The dilation `S = [[0, Cᵀ], [C, 0]]` has the explicit orthonormal
eigenbasis (`wD`)

  `(e_{inl k} + e_{inr k})/√2` (eigenvalue `σₖ`), `(e_{inl k} - e_{inr k})/√2` (eigenvalue `-σₖ`)
  for `k < min(M, N)`, and the remaining coordinate vectors (eigenvalue `0`).

Gradient flow from any **balanced** start `ε (A₀, B₀)` (`A₀ A₀ᵀ = B₀ᵀ B₀`) gives `P = Z Zᵀ`
equal to the Riccati closed form (`BalancedFlow`, `Riccati.eq_Pc`), whose entries on the
plateau window are known (`Riccati.Pc_entries_limit`). Reading off the block `B A`:

  `(B A)(t) → diag(σₖ · 1[σₖ c₁ > 1])` uniformly on `[c₁, c₂] · log(1/ε)`   (`balanced_plateau_diag`),

provided the signal directions `Z₀ᵀ (e_{inl k} + e_{inr k})/√2 = (A₀ eₖ + B₀ᵀ eₖ)/√2` are
linearly independent (they admit dual vectors). No alignment of the start with the data.
-/

noncomputable section
open Real Filter Topology Matrix Set
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRisk OpenTheory.TruncationRank OpenTheory.TruncationEvent

namespace OpenTheory.Plateau

variable {M N H : ℕ}

local notation "VS" => EuclideanSpace ℝ (Fin M ⊕ Fin N)

/-- Coordinate vectors. -/
def eL (j : Fin M) : VS := EuclideanSpace.single (Sum.inl j) 1
def eR (i : Fin N) : VS := EuclideanSpace.single (Sum.inr i) 1

/-- The explicit eigenbasis of the dilation of diagonal data. -/
def wvec : Fin M ⊕ Fin N → VS
  | Sum.inl j => if h : (j : ℕ) < N then (√2)⁻¹ • (eL j + eR ⟨j, h⟩) else eL j
  | Sum.inr i => if h : (i : ℕ) < M then (√2)⁻¹ • (eL ⟨i, h⟩ - eR i) else eR i

/-- Its eigenvalues. -/
def lamD (σ : ℕ → ℝ) : Fin M ⊕ Fin N → ℝ
  | Sum.inl j => if (j : ℕ) < N then σ j else 0
  | Sum.inr i => if (i : ℕ) < M then -σ i else 0

theorem inner_eL_eL (j j' : Fin M) : ⟪(eL j : VS), eL j'⟫ = if j = j' then 1 else 0 := by
  simp [eL, EuclideanSpace.inner_single_left, PiLp.single_apply]
theorem inner_eR_eR (i i' : Fin N) : ⟪(eR i : VS), eR i'⟫ = if i = i' then 1 else 0 := by
  simp [eR, EuclideanSpace.inner_single_left, PiLp.single_apply]
theorem inner_eL_eR (j : Fin M) (i : Fin N) : ⟪(eL j : VS), eR i⟫ = 0 := by
  simp [eL, eR, EuclideanSpace.inner_single_left]
theorem inner_eR_eL (i : Fin N) (j : Fin M) : ⟪(eR i : VS), eL j⟫ = 0 := by
  simp [eL, eR, EuclideanSpace.inner_single_left]

theorem norm_eL (j : Fin M) : ‖(eL j : VS)‖ = 1 := by simp [eL]
theorem norm_eR (i : Fin N) : ‖(eR i : VS)‖ = 1 := by simp [eR]

theorem sqrt2_inv_sq : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem orthonormal_wvec : Orthonormal ℝ (wvec (M := M) (N := N)) := by
  classical
  rw [orthonormal_iff_ite]
  have s2 := sqrt2_inv_sq
  rintro (j | i) (j' | i') <;> simp only [wvec] <;> split_ifs <;>
    simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_eL_eL, inner_eR_eR, inner_eL_eR, inner_eR_eL,
      conj_trivial, Fin.ext_iff,
      ] <;>
    (try split_ifs) <;> (try simp_all) <;> (try omega) <;> (try nlinarith [s2])

/-- The eigenbasis as an orthonormal basis. -/
def wD : OrthonormalBasis (Fin M ⊕ Fin N) ℝ VS :=
  OrthonormalBasis.mk orthonormal_wvec (by
    rw [orthonormal_wvec.linearIndependent.span_eq_top_of_card_eq_finrank']
    simp [finrank_euclideanSpace])

theorem wD_apply (a : Fin M ⊕ Fin N) : (wD : OrthonormalBasis _ ℝ VS) a = wvec a := by
  simp [wD]

/-- The dilation of diagonal data on coordinate vectors. -/
theorem S_eL (σ : ℕ → ℝ) (j : Fin M) :
    cl (Smat (diagData (N := N) σ)) (eL j) = if h : (j : ℕ) < N then σ j • eR ⟨j, h⟩ else 0 := by
  ext (k | i)
  · simp [cl, eL, Smat, Matrix.mulVec, dotProduct, Matrix.fromBlocks]
    split_ifs <;> simp [eR]
  · simp only [cl, eL, Smat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      PiLp.toLp_apply, Matrix.mulVec, dotProduct, PiLp.ofLp_single]
    simp [Matrix.fromBlocks, diagData, Pi.single_apply]
    split_ifs with h1 h2 h2 <;> (simp_all [eR, PiLp.single_apply, Fin.ext_iff]; try omega)

theorem S_eR (σ : ℕ → ℝ) (i : Fin N) :
    cl (Smat (diagData (M := M) σ)) (eR i) = if h : (i : ℕ) < M then σ i • eL ⟨i, h⟩ else 0 := by
  ext (k | i')
  · simp only [cl, eR, Smat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
      PiLp.toLp_apply, Matrix.mulVec, dotProduct, PiLp.ofLp_single]
    simp [Matrix.fromBlocks, diagData, Pi.single_apply]
    split_ifs with h1 h2 h2 <;> simp_all [eL, Fin.ext_iff]
  · simp [cl, eR, Smat, Matrix.mulVec, dotProduct, Matrix.fromBlocks]
    split_ifs <;> simp [eL]

theorem S_wvec (σ : ℕ → ℝ) (a : Fin M ⊕ Fin N) :
    cl (Smat (diagData σ)) (wvec a) = lamD σ a • wvec a := by
  rcases a with j | i
  · simp only [wvec, lamD]
    split_ifs with h
    · rw [map_smul, map_add, S_eL, S_eR, dite_eq_left h, dite_eq_left j.2]
      simp only [smul_add, smul_smul]
      rw [add_comm]; congr 2 <;> ring_nf
    · rw [S_eL, dite_eq_right h, zero_smul]
  · simp only [wvec, lamD]
    split_ifs with h
    · rw [map_smul, map_sub, S_eL, S_eR, dite_eq_left h, dite_eq_left i.2]
      ext (k | k) <;> simp [eL, eR, PiLp.single_apply, Fin.ext_iff] <;> split_ifs <;> ring
    · rw [S_eR, dite_eq_right h, zero_smul]

theorem Sop_wD (σ : ℕ → ℝ) :
    Riccati.Sop (wD (M := M) (N := N)) (lamD σ) = cl (Smat (diagData σ)) := by
  classical
  refine ContinuousLinearMap.coe_injective ((wD (M := M) (N := N)).toBasis.ext fun a => ?_)
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [wD_apply, S_wvec, Riccati.Sop]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    Riccati.proj_apply]
  rw [Finset.sum_eq_single a]
  · simp only [wD_apply]
    rw [real_inner_self_eq_norm_sq, orthonormal_wvec.1 a]; simp
  · intro b _ hb
    simp only [wD_apply]
    rw [orthonormal_wvec.2 hb]; simp
  · simp

/-- The network product is an off-diagonal entry of `P`. -/
theorem prodBA_eq_inner (p : State M N H) (i : Fin N) (j : Fin M) :
    prodBA p i j = ⟪(eR i : VS), Pop p (eL j)⟫ := by
  rw [Pop, adjoint_cl, ← cl_mul]
  simp only [cl, eR, eL, EuclideanSpace.inner_single_left, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.ofLp_single, Pi.single_apply]
  simp [Matrix.mul_apply, Zmat, Amat, Bmat, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    prodBA, mul_comm]

theorem Zmat_smul (c : ℝ) (p : State M N H) : Zmat (c • p) = c • Zmat p := by
  ext (i | i) j <;> simp [Zmat, Amat, Bmat, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]

theorem gap_smul (c : ℝ) (p : State M N H) : gap (c • p) = c ^ 2 • gap p := by
  have hA : Amat (c • p) = c • Amat p := by ext; simp [Amat]
  have hB : Bmat (c • p) = c • Bmat p := by ext; simp [Bmat]
  simp only [gap, hA, hB, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_sub, sq]

/-- Expansion of an entry in the eigenbasis. -/
theorem inner_expand (P : VS →L[ℝ] VS) (u v : VS) :
    ⟪u, P v⟫ = ∑ a, ∑ b, ⟪wD a, u⟫ * ⟪wD b, v⟫ * ⟪wD a, P (wD b)⟫ := by
  conv_lhs => rw [← (wD (M := M) (N := N)).sum_repr' u, ← (wD (M := M) (N := N)).sum_repr' v]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem inner_wD_inl_eR (k : Fin M) (i : Fin N) :
    ⟪(wD (M := M) (N := N)) (Sum.inl k), eR i⟫ =
      if (k : ℕ) < N ∧ (k : ℕ) = i then (√2)⁻¹ else 0 := by
  rw [wD_apply]; simp only [wvec]
  split_ifs with h1 h2 h2 <;>
    simp_all [inner_add_left, real_inner_smul_left, inner_eL_eR, inner_eR_eR, Fin.ext_iff, norm_eR]

theorem inner_wD_inl_eL (k j : Fin M) :
    ⟪(wD (M := M) (N := N)) (Sum.inl k), eL j⟫ =
      if (k : ℕ) < N then (if k = j then (√2)⁻¹ else 0) else (if k = j then 1 else 0) := by
  rw [wD_apply]; simp only [wvec]
  split_ifs with h1 h2 h2 <;>
    simp_all [inner_add_left, real_inner_smul_left, inner_eL_eL, inner_eR_eL, norm_eL]

/-- The limit value, read off in coordinates. -/
theorem target_expand (σ : ℕ → ℝ) (hσ0 : ∀ k, 0 ≤ σ k) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (i : Fin N) (j : Fin M) :
    ∑ a, ∑ b, ⟪(wD (M := M) (N := N)) a, eR i⟫ * ⟪wD b, eL j⟫ *
        (if a = b ∧ a ∈ Finset.univ.filter (fun a => 1 < lamD σ a * c₁) then 2 * lamD σ a else 0) =
      if (i : ℕ) = j ∧ 1 < σ i * c₁ then σ i else 0 := by
  classical
  have hinner : ∀ a, ∑ b, ⟪(wD (M := M) (N := N)) a, eR i⟫ * ⟪wD b, eL j⟫ *
      (if a = b ∧ a ∈ Finset.univ.filter (fun a => 1 < lamD σ a * c₁) then 2 * lamD σ a else 0) =
      ⟪wD a, eR i⟫ * ⟪wD a, eL j⟫ * (if 1 < lamD σ a * c₁ then 2 * lamD σ a else 0) := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [hinner, Fintype.sum_sum_type]
  have hR : ∀ i' : Fin N, (if 1 < lamD σ (Sum.inr i' : Fin M ⊕ Fin N) * c₁ then
      2 * lamD σ (Sum.inr i' : Fin M ⊕ Fin N) else 0) = 0 := by
    intro i'
    rw [ite_eq_right]
    intro h
    simp only [lamD] at h
    split_ifs at h <;> nlinarith [hσ0 i']
  simp only [hR, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single j]
  · rw [inner_wD_inl_eR, inner_wD_inl_eL]
    simp only [lamD]
    by_cases hjN : (j : ℕ) < N
    · by_cases hij : (i : ℕ) = j
      · simp only [hij, hjN, and_self, true_and, ite_true]
        split_ifs with h1
        · rw [← mul_assoc, sqrt2_inv_sq]; ring
        · simp
      · have hji : ¬ (j : ℕ) = i := fun h => hij h.symm
        simp [hji, hij]
    · have hij : ¬ (i : ℕ) = j := by omega
      simp [hjN, hij]
  · intro k _ hkj
    rw [inner_wD_inl_eL]
    simp [hkj]
  · simp

/-- **The plateau from a balanced start (diagonal data).** No alignment of the start with the
data: any balanced shape `p₀` whose signal directions admit dual vectors. -/
theorem balanced_plateau_diag {σ : ℕ → ℝ} (hσ0 : ∀ k, 0 ≤ σ k) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₂ : 0 ≤ c₂) (hsplit : ∀ k : ℕ, k < M → k < N → 1 < σ k * c₁ ∨ σ k * c₂ < 1)
    (p₀ : State M N H) (hbal : gap p₀ = 0) (d : Fin M ⊕ Fin N → EuclideanSpace ℝ (Fin H))
    (hd : ∀ a ∈ Finset.univ.filter (fun a => 1 < lamD σ a * c₁),
      ∀ b ∈ Finset.univ.filter (fun a => 1 < lamD σ a * c₁),
        ⟪Riccati.gvec (wD (M := M) (N := N)) (cl (Zmat p₀)) a, d b⟫ = if a = b then 1 else 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H,
      (∀ t, HasDerivAt f (gradField (diagData σ) (f t)) t) → f 0 = ε • p₀ →
      ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)), ∀ i j,
        |prodBA (f t) i j - (if (i : ℕ) = j ∧ 1 < σ i * c₁ then σ i else 0)| < δ := by
  classical
  set s := Finset.univ.filter (fun a : Fin M ⊕ Fin N => 1 < lamD σ a * c₁)
  have hsig : ∀ a ∈ s, 1 < lamD σ a * c₁ := fun a ha => (Finset.mem_filter.1 ha).2
  have hnoise : ∀ a ∉ s, lamD σ a * c₂ < 1 := by
    intro a ha
    have ha' : ¬ 1 < lamD σ a * c₁ := fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rcases a with j | i
    · simp only [lamD] at ha' ⊢
      split_ifs with hj
      · rw [ite_eq_left hj] at ha'
        exact (hsplit j j.2 hj).resolve_left ha'
      · simp
    · simp only [lamD]
      split_ifs
      · nlinarith [hσ0 i]
      · simp
  set K : ℝ := ((Fintype.card (Fin M ⊕ Fin N) : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set δ' := δ / (K ^ 2 + 1)
  have hδ' : 0 < δ' := by positivity
  have E := Riccati.Pc_entries_limit (wD (M := M) (N := N)) (lamD σ) (cl (Zmat p₀)) s hc₁ hc₂
    hsig hnoise d hd hδ'
  filter_upwards [E, Riccati.eventually_small] with ε hE ⟨h0, h1⟩ f hf hf0 t ht i j
  have hlog := Riccati.log_inv_nonneg h0 h1
  have ht0 : 0 ≤ t := le_trans (mul_nonneg hc₁.le hlog) ht.1
  -- the trajectory's `P` is the closed form
  have hbal0 : gap (f 0) = 0 := by rw [hf0, gap_smul, hbal, smul_zero]
  have hPc : Pop (f t) = Riccati.Pc (wD (M := M) (N := N)) (lamD σ) (ε • cl (Zmat p₀)) t := by
    have h := Riccati.eq_Pc (wD (M := M) (N := N)) (lamD σ) (ε • cl (Zmat p₀)) (T := t)
      (P := fun s => Pop (f s))
      (fun s _ => (hasDerivAt_Pop (diagData σ) hf hbal0 s).continuousAt.continuousWithinAt)
      (fun s _ => by
        rw [Sop_wD]; exact (hasDerivAt_Pop (diagData σ) hf hbal0 s).hasDerivWithinAt)
      (by rw [Pop, hf0, Zmat_smul, cl_smul])
    exact h ⟨ht0, le_rfl⟩
  rw [prodBA_eq_inner, hPc, inner_expand, ← target_expand σ hσ0 hc₁ i j, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  have hcoef : ∀ (a : Fin M ⊕ Fin N) (v : EuclideanSpace ℝ (Fin M ⊕ Fin N)), ‖v‖ = 1 →
      |⟪(wD (M := M) (N := N)) a, v⟫| ≤ 1 := fun a v hv => by
    have := abs_real_inner_le_norm ((wD (M := M) (N := N)) a) v
    rwa [wD.orthonormal.1 a, hv, one_mul] at this
  calc |∑ a, ∑ b, ⟪wD a, eR i⟫ * ⟪wD b, eL j⟫ *
          (⟪wD a, Riccati.Pc wD (lamD σ) (ε • cl (Zmat p₀)) t (wD b)⟫ -
            (if a = b ∧ a ∈ s then 2 * lamD σ a else 0))|
      ≤ ∑ a : Fin M ⊕ Fin N, ∑ b : Fin M ⊕ Fin N, δ' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [abs_mul, abs_mul]
        have h1 := hcoef a (eR i) (norm_eR i)
        have h2 := hcoef b (eL j) (norm_eL j)
        have h3 := (hE t ht a b).le
        calc |⟪wD a, eR i⟫| * |⟪wD b, eL j⟫| * |_| ≤ 1 * 1 * δ' := by
              gcongr
          _ = δ' := by ring
    _ = K ^ 2 * δ' := by simp [K, Finset.sum_const, sq]; ring
    _ < δ := by
        simp only [δ']
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

theorem gap_rotate {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (q : State M N H) : gap (rotate U V q) = gap q := by
  have hA : Amat (rotate U V q) = Amat q * V := rfl
  have hB : Bmat (rotate U V q) = Uᵀ * Bmat q := rfl
  rw [gap, gap, hA, hB, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul, Matrix.mul_assoc (Bmat q)ᵀ,
    ← Matrix.mul_assoc U, hU, Matrix.one_mul]

theorem rotate_smul (U : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin M) (Fin M) ℝ) (c : ℝ)
    (q : State M N H) : rotate U V (c • q) = c • rotate U V q := by
  simp only [rotate]
  refine Prod.ext ?_ ?_
  · show Matrix.of (c • q).1 * V = c • (Matrix.of q.1 * V)
    rw [← Matrix.smul_mul]; rfl
  · show Uᵀ * Matrix.of (c • q).2 = c • (Uᵀ * Matrix.of q.2)
    rw [← Matrix.mul_smul]; rfl

/-- **Balanced start, general data: the plateau is the truncated SVD.** On the good event
(`‖C Cᵀ - W Wᵀ‖ ≤ s2/4`), from any balanced start `ε q₀` whose signal directions (in the
data's singular basis) admit dual vectors, gradient flow reaches at time `√(2/s2) log(1/ε)`,
as `ε → 0`, the truncated SVD `trunc (s2/2) C`. -/
theorem balanced_plateau_eq_trunc {C W : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ)
    (hσ0 : ∀ k, 0 ≤ σ k) {s2 : ℝ} (hs2 : 0 < s2)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i = 0)
    (hclose : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ s2 / 4)
    (q₀ : State M N H) (hbal : gap q₀ = 0) (d : Fin M ⊕ Fin N → EuclideanSpace ℝ (Fin H))
    (hd : ∀ a ∈ Finset.univ.filter (fun a => 1 < lamD σ a * √(2 / s2)),
      ∀ b ∈ Finset.univ.filter (fun a => 1 < lamD σ a * √(2 / s2)),
        ⟪Riccati.gvec (wD (M := M) (N := N)) (cl (Zmat (rotate U V q₀))) a, d b⟫ =
          if a = b then 1 else 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H, (∀ t, HasDerivAt f (gradField C (f t)) t) →
      f 0 = ε • q₀ → ∀ i j,
        |prodBA (f (√(2 / s2) * log (1 / ε))) i j -
          toEuclideanLin.symm (trunc finrank_EN (toEuclideanLin C) (s2 / 2)) i j| < δ := by
  set c := √(2 / s2)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 2 / s2 := Real.sq_sqrt (by positivity)
  -- classification of the singular values on the good event
  have hcls : ∀ k : ℕ, k < M → k < N → (s2 / 2 ≤ σ k ^ 2 → 1 < σ k * c) ∧
      (σ k ^ 2 < s2 / 2 → σ k * c < 1) := by
    intro k hkM hkN
    have hev : ev (M := M) σ (⟨k, hkN⟩ : Fin N) = σ k ^ 2 := by simp [ev, hkM]
    have heig := gramL_col hU hV hsvd (⟨k, hkN⟩ : Fin N)
    rw [hev] at heig
    obtain ⟨hs, hn⟩ := eigenvalue_split (τ := s2 / 2) (h := s2 / 4) finrank_EN hWL hclose
      (by linarith) (by linarith) ((orthonormal_col hU).ne_zero _) heig
    constructor
    · intro hk
      have h1 := hs hk
      have : (1 : ℝ) ^ 2 < (σ k * c) ^ 2 := by
        rw [mul_pow, hc2, one_pow]
        have : σ k ^ 2 * (2 / s2) ≥ (3 * s2 / 4) * (2 / s2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have e : (3 * s2 / 4) * (2 / s2) = 3 / 2 := by field_simp; ring
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (mul_nonneg (hσ0 k) hc.le) this
    · intro hk
      have h1 := hn hk
      have : (σ k * c) ^ 2 < (1 : ℝ) ^ 2 := by
        rw [mul_pow, hc2, one_pow]
        have : σ k ^ 2 * (2 / s2) ≤ (s2 / 4) * (2 / s2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have e : (s2 / 4) * (2 / s2) = 1 / 2 := by field_simp; ring
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 zero_le_one this
  have hsplit : ∀ k : ℕ, k < M → k < N → 1 < σ k * c ∨ σ k * c < 1 := by
    intro k hkM hkN
    by_cases hk : s2 / 2 ≤ σ k ^ 2
    · exact Or.inl ((hcls k hkM hkN).1 hk)
    · exact Or.inr ((hcls k hkM hkN).2 (lt_of_not_ge hk))
  have hNM : (0 : ℝ) < N * M + 1 := by positivity
  set δ' := δ / (N * M + 1)
  have hδ' : 0 < δ' := div_pos hδ hNM
  have E := balanced_plateau_diag hσ0 hc hc.le hsplit (rotate U V q₀)
    ((gap_rotate hU hV q₀).trans hbal) d hd hδ'
  filter_upwards [E, Riccati.eventually_small] with ε hE ⟨h0, h1⟩ f hf hf0 i j
  have hlog := Riccati.log_inv_nonneg h0 h1
  set t := c * log (1 / ε)
  let g : ℝ → State M N H := fun s => rotate U V (f s)
  have hg : ∀ s, HasDerivAt g (gradField (diagData σ) (g s)) s := fun s => by
    have := rotate_solves hU hV C (hf s); rwa [hsvd] at this
  have hg0 : g 0 = ε • rotate U V q₀ := by simp only [g, hf0, rotate_smul]
  have hG := hE g hg hg0 t ⟨le_rfl, le_rfl⟩
  -- the limit matrix is the kept part of `diag σ`
  set L : Matrix (Fin N) (Fin M) ℝ := Matrix.of (fun (a : Fin N) (b : Fin M) =>
    if (a : ℕ) = b ∧ 1 < σ a * c then σ a else 0)
  have hL : L = diagData (keep σ (s2 / 2)) := by
    ext a b
    simp only [L, Matrix.of_apply, diagData, keep]
    by_cases hab : (a : ℕ) = b
    · have hbM : (a : ℕ) < M := hab ▸ b.2
      rw [ite_eq_left hab]
      by_cases hk : s2 / 2 ≤ σ a ^ 2
      · rw [ite_eq_left ⟨hab, (hcls a hbM a.2).1 hk⟩, ite_eq_left hk]
      · have h' : ¬ ((a : ℕ) = b ∧ 1 < σ a * c) := fun h =>
          absurd ((hcls a hbM a.2).2 (lt_of_not_ge hk)) (not_lt.2 h.2.le)
        rw [ite_eq_right h', ite_eq_right hk]
    · rw [ite_eq_right (fun h => hab h.1), ite_eq_right hab]
  have hP : Matrix.of (prodBA (f t)) = U * Matrix.of (prodBA (g t)) * Vᵀ := by
    have hP' := prodBA_rotate U V (f t)
    have hUU := transpose_mul_self_of_mul_transpose hU
    rw [show Matrix.of (prodBA (g t)) = Uᵀ * Matrix.of (prodBA (f t)) * V from hP']
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc _ V, hV, Matrix.mul_one]
  have hdiff : Matrix.of (prodBA (f t)) - U * L * Vᵀ = U * (Matrix.of (prodBA (g t)) - L) * Vᵀ := by
    rw [hP, Matrix.mul_sub, Matrix.sub_mul]
  have hb := abs_conj_entry_le hU hV (D := Matrix.of (prodBA (g t)) - L) (δ := δ')
    (fun a b => (hG a b).le) i j
  rw [← hdiff] at hb
  rw [trunc_eq_svd hU hV hsvd, LinearEquiv.symm_apply_apply, ← hL]
  calc |prodBA (f t) i j - (U * L * Vᵀ) i j| ≤ N * M * δ' := hb
    _ < δ := by
      rw [show (N : ℝ) * M * δ' = δ * ((N * M) / (N * M + 1)) by simp only [δ']; ring]
      exact mul_lt_of_lt_one_right hδ ((div_lt_one hNM).2 (by linarith))

end OpenTheory.Plateau
