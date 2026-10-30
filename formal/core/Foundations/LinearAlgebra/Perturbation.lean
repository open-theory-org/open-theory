import Foundations.LinearAlgebra.RankTruncation
import Foundations.LinearAlgebra.HilbertSchmidt

/-!
# Second-order perturbation of the rank truncation

Let `W, C : E → F`, `D = C - W`, and suppose every nonzero eigenvalue of `W Wᵀ` and of
`Wᵀ W` is at least `s2 > 0` (nonzero singular values of `W` at least `√s2`). For a
threshold `0 < τ < s2`, the truncation `trunc C = P_{[τ,∞)}(C Cᵀ) ∘ C` keeps the
singular directions of `C` with `σ² ≥ τ`. With `P, Q` the projections onto the column
and row spaces of `W` and `P_T(D) = D - P⊥ D Q⊥` the projection onto the tangent space
of the rank-`r` matrices at `W`,

  `hs(trunc C - W - P_T(D)) ≤ K₁ h_L h_R hs(W) + K₂ (h_L + h_R) hs(D)`,

where `h_L = ‖C Cᵀ - W Wᵀ‖ ≤ ‖D‖ (2‖W‖ + ‖D‖)` and similarly `h_R`
(`second_order_bound`). Both terms are of second order in `D`, with no smallness
condition: the proof uses only Davis–Kahan bounds (vendored SLT) and the intertwining
`P ∘ C = C ∘ Q` of `RankTruncation`.

Statistical use: `TruncationRisk` (the `√n`-rescaled remainder vanishes).
-/

noncomputable section
open LinearMap Submodule OpenTheory.HilbertSchmidt OpenTheory.RankTruncation

namespace OpenTheory.Perturbation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Operator-norm helpers -/

theorem toCLM_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : F →ₗ[ℝ] G) (B : E →ₗ[ℝ] F) :
    LinearMap.toContinuousLinearMap (A ∘ₗ B) =
      (LinearMap.toContinuousLinearMap A).comp (LinearMap.toContinuousLinearMap B) := rfl

theorem opn_comp_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : F →ₗ[ℝ] G) (B : E →ₗ[ℝ] F) : opn (A ∘ₗ B) ≤ opn A * opn B := by
  unfold opn; rw [toCLM_comp]; exact ContinuousLinearMap.opNorm_comp_le _ _

omit [FiniteDimensional ℝ F] in
theorem opn_add_le (A B : E →ₗ[ℝ] F) : opn (A + B) ≤ opn A + opn B := by
  unfold opn; rw [map_add]; exact norm_add_le _ _

omit [FiniteDimensional ℝ F] in
theorem opn_sub_le (A B : E →ₗ[ℝ] F) : opn (A - B) ≤ opn A + opn B := by
  unfold opn; rw [map_sub]; exact norm_sub_le _ _

omit [FiniteDimensional ℝ F] in
theorem opn_sub_comm (A B : E →ₗ[ℝ] F) : opn (A - B) = opn (B - A) := by
  unfold opn; rw [map_sub, map_sub, norm_sub_rev]

/-- `‖A ∘ B‖ = ‖B ∘ A‖` for symmetric `A, B` (take adjoints). -/
theorem opn_comp_swap {A B : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    opn (A ∘ₗ B) = opn (B ∘ₗ A) := by
  rw [← opn_adjoint (A ∘ₗ B), LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq]

/-- Spectral projections are symmetric. -/
theorem spectralProjection_isSymmetric {A : E →ₗ[ℝ] E} {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (S : Set ℝ) : (hA.spectralProjection hn S).IsSymmetric :=
  (hA.spectralSubspace hn S).starProjection_isSymmetric

theorem opn_spectralProjection_le {A : E →ₗ[ℝ] E} {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (S : Set ℝ) : opn (hA.spectralProjection hn S) ≤ 1 :=
  (hA.spectralSubspace hn S).starProjection_norm_le

/-- Spectral projections agree when the two sets select the same eigenvalues. -/
theorem spectralProjection_congr {A : E →ₗ[ℝ] E} {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank ℝ E = n) {S T : Set ℝ} (h : ∀ i, hA.eigenvalues hn i ∈ S ↔ hA.eigenvalues hn i ∈ T) :
    hA.spectralProjection hn S = hA.spectralProjection hn T := by
  have : hA.spectralSubspace hn S = hA.spectralSubspace hn T := by
    simp only [LinearMap.IsSymmetric.spectralSubspace]
    congr 1
    ext x
    simp only [Set.mem_range, Subtype.exists]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, (h i).1 hi, hx⟩, fun ⟨i, hi, hx⟩ => ⟨i, (h i).2 hi, hx⟩⟩
  simp only [LinearMap.IsSymmetric.spectralProjection, this]

/-! ### The Gram perturbation -/

theorem gramL_add_sub (W D : E →ₗ[ℝ] F) :
    gramL (W + D) - gramL W =
      W ∘ₗ LinearMap.adjoint D + D ∘ₗ LinearMap.adjoint W + D ∘ₗ LinearMap.adjoint D := by
  ext x
  simp only [gramL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  abel

theorem gramR_add_sub (W D : E →ₗ[ℝ] F) :
    gramR (W + D) - gramR W =
      LinearMap.adjoint W ∘ₗ D + LinearMap.adjoint D ∘ₗ W + LinearMap.adjoint D ∘ₗ D := by
  ext x
  simp only [gramR, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  abel

/-- `‖C Cᵀ - W Wᵀ‖ ≤ ‖D‖ (2‖W‖ + ‖D‖)` with `D = C - W`. -/
theorem opn_gramL_sub_le (C W : E →ₗ[ℝ] F) :
    opn (gramL C - gramL W) ≤ opn (C - W) * (2 * opn W + opn (C - W)) := by
  obtain ⟨D, rfl⟩ : ∃ D, C = W + D := ⟨C - W, by abel⟩
  rw [add_sub_cancel_left, gramL_add_sub]
  have h1 := opn_comp_le W (LinearMap.adjoint D)
  have h2 := opn_comp_le D (LinearMap.adjoint W)
  have h3 := opn_comp_le D (LinearMap.adjoint D)
  rw [opn_adjoint] at h1 h2 h3
  have h12 := opn_add_le (W ∘ₗ LinearMap.adjoint D) (D ∘ₗ LinearMap.adjoint W)
  have h123 := opn_add_le (W ∘ₗ LinearMap.adjoint D + D ∘ₗ LinearMap.adjoint W)
    (D ∘ₗ LinearMap.adjoint D)
  calc _ ≤ opn W * opn D + opn D * opn W + opn D * opn D := by linarith
    _ = opn D * (2 * opn W + opn D) := by ring

/-- `‖Cᵀ C - Wᵀ W‖ ≤ ‖D‖ (2‖W‖ + ‖D‖)`. -/
theorem opn_gramR_sub_le (C W : E →ₗ[ℝ] F) :
    opn (gramR C - gramR W) ≤ opn (C - W) * (2 * opn W + opn (C - W)) := by
  obtain ⟨D, rfl⟩ : ∃ D, C = W + D := ⟨C - W, by abel⟩
  rw [add_sub_cancel_left, gramR_add_sub]
  have h1 := opn_comp_le (LinearMap.adjoint W) D
  have h2 := opn_comp_le (LinearMap.adjoint D) W
  have h3 := opn_comp_le (LinearMap.adjoint D) D
  rw [opn_adjoint] at h1 h2 h3
  have h12 := opn_add_le (LinearMap.adjoint W ∘ₗ D) (LinearMap.adjoint D ∘ₗ W)
  have h123 := opn_add_le (LinearMap.adjoint W ∘ₗ D + LinearMap.adjoint D ∘ₗ W)
    (LinearMap.adjoint D ∘ₗ D)
  calc _ ≤ opn W * opn D + opn D * opn W + opn D * opn D := by linarith
    _ = opn D * (2 * opn W + opn D) := by ring

/-! ### Projections of `W` and `C` -/

section Projections

variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)

/-- Top and bottom spectral projections, left (output) side. -/
def Ptop (C : E →ₗ[ℝ] F) (τ : ℝ) : F →ₗ[ℝ] F := projL hF C (Set.Ici τ)
def Pbot (C : E →ₗ[ℝ] F) (τ : ℝ) : F →ₗ[ℝ] F := projL hF C (Set.Ici τ)ᶜ
/-- Top and bottom spectral projections, right (input) side. -/
def Qtop (C : E →ₗ[ℝ] F) (τ : ℝ) : E →ₗ[ℝ] E := projR hE C (Set.Ici τ)
def Qbot (C : E →ₗ[ℝ] F) (τ : ℝ) : E →ₗ[ℝ] E := projR hE C (Set.Ici τ)ᶜ

theorem Ptop_add_Pbot (C : E →ₗ[ℝ] F) (τ : ℝ) (y : F) : Ptop hF C τ y + Pbot hF C τ y = y :=
  spectralProjection_add_compl _ hF _ y

theorem Qtop_add_Qbot (C : E →ₗ[ℝ] F) (τ : ℝ) (x : E) : Qtop hE C τ x + Qbot hE C τ x = x :=
  spectralProjection_add_compl _ hE _ x

theorem Ptop_C (C : E →ₗ[ℝ] F) (τ : ℝ) (x : E) : Ptop hF C τ (C x) = C (Qtop hE C τ x) :=
  LinearMap.congr_fun (projL_comp hE hF C (Set.Ici τ)) x

theorem Pbot_C (C : E →ₗ[ℝ] F) (τ : ℝ) (x : E) : Pbot hF C τ (C x) = C (Qbot hE C τ x) :=
  LinearMap.congr_fun (projL_comp hE hF C (Set.Ici τ)ᶜ) x

theorem Pbot_idem (C : E →ₗ[ℝ] F) (τ : ℝ) (y : F) : Pbot hF C τ (Pbot hF C τ y) = Pbot hF C τ y := by
  simp only [Pbot, projL, LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)

/-- **Kernel**: if every eigenvalue of `Wᵀ W` below `s2` is `0`, then `W` vanishes on the
bottom spectral subspace. -/
theorem W_Qbot {W : E →ₗ[ℝ] F} {s2 : ℝ}
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0) (x : E) :
    W (Qbot hE W s2 x) = 0 := by
  have hmem : Qbot hE W s2 x ∈ (gramR_isSymmetric W).spectralSubspace hE (Set.Ici s2)ᶜ :=
    (gramR_isSymmetric W).spectralProjection_apply_mem hE _ x
  generalize Qbot hE W s2 x = v at hmem ⊢
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy
    have h0 := hWR i hi
    have hev := (gramR_isSymmetric W).apply_eigenvectorBasis hE i
    rw [h0, RCLike.ofReal_zero, zero_smul] at hev
    dsimp only
    rw [← norm_eq_zero, ← sq_eq_zero_iff, ← real_inner_self_eq_norm_sq,
      ← LinearMap.adjoint_inner_left]
    exact (show LinearMap.adjoint W (W _) = 0 from hev) ▸ inner_zero_left _
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul a y _ hy => rw [map_smul, hy, smul_zero]

/-- `W = P W Q`: `W x = Ptop W (W (Qtop W x))`. -/
theorem W_eq_PWQ {W : E →ₗ[ℝ] F} {s2 : ℝ}
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0) (x : E) :
    W x = Ptop hF W s2 (W (Qtop hE W s2 x)) := by
  have hWQ : W (Qtop hE W s2 x) = W x := by
    conv_rhs => rw [← Qtop_add_Qbot hE W s2 x]
    rw [map_add, W_Qbot hE hWR, add_zero]
  rw [Ptop_C hE hF, show Qtop hE W s2 (Qtop hE W s2 x) = Qtop hE W s2 x from by
    simp only [Qtop, projR, LinearMap.IsSymmetric.spectralProjection, ContinuousLinearMap.coe_coe]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _), hWQ]

end Projections

/-! ### Davis–Kahan bounds -/

section DavisKahan

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Davis–Kahan in our notation: `‖P_J(B) P_I(A)‖ ≤ ‖A - B‖ / δ`. -/
theorem dk {A B : G →ₗ[ℝ] G} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hn : Module.finrank ℝ G = n)
    {I J : Set ℝ} {δ : ℝ} (hI : I.OrdConnected) (hδ : 0 < δ) (hsep : Set.SeparatedBy δ I J) :
    opn (hB.spectralProjection hn J ∘ₗ hA.spectralProjection hn I) ≤ opn (A - B) / δ :=
  hA.davisKahan_spectralProjection_hdp hB hn hI hδ hsep

theorem sep_top {s2 τ : ℝ} (h : τ ≤ s2) : Set.SeparatedBy (s2 - τ) (Set.Ici s2) (Set.Ici τ)ᶜ := by
  intro x hx y hy
  simp only [Set.mem_Ici, Set.mem_compl_iff, not_le] at hx hy
  rw [abs_of_nonneg (by linarith)]; linarith

theorem sep_bot {τ : ℝ} (h : 0 ≤ τ) : Set.SeparatedBy τ (Set.Iic 0) (Set.Ici τ) := by
  intro x hx y hy
  simp only [Set.mem_Iic, Set.mem_Ici] at hx hy
  rw [abs_of_nonpos (by linarith)]; linarith

/-- The bottom projection of `W` equals the projection onto eigenvalue `≤ 0`. -/
theorem bot_congr {A : G →ₗ[ℝ] G} (hA : A.IsSymmetric) (hn : Module.finrank ℝ G = n) {s2 : ℝ}
    (hs2 : 0 < s2) (hW : ∀ i, hA.eigenvalues hn i ∉ Set.Ici s2 → hA.eigenvalues hn i = 0) :
    hA.spectralProjection hn (Set.Ici s2)ᶜ = hA.spectralProjection hn (Set.Iic 0) := by
  apply spectralProjection_congr
  intro i
  simp only [Set.mem_compl_iff, Set.mem_Ici, Set.mem_Iic, not_le]
  constructor
  · intro h; exact (hW i (by simpa using h)).le
  · intro h; linarith

end DavisKahan

/-! ### The second-order bound -/

section Main

variable {m p : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = p)
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Second-order perturbation of the rank truncation.** With `hL = ‖W Wᵀ - C Cᵀ‖`,
`hR = ‖Wᵀ W - Cᵀ C‖`, `δ = s2 - τ` and `D = C - W`,

  `hs(trunc C - W - P_T D) ≤ (hL/δ)(hR/δ) hs(W) + (hL/δ + hL/τ + hR/δ + hR/τ) hs(D)`. -/
theorem second_order_bound (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis κ ℝ F)
    {C W : E →ₗ[ℝ] F} {s2 τ : ℝ} (hτ : 0 < τ) (hτs : τ < s2)
    (hWL : ∀ i, (gramL_isSymmetric W).eigenvalues hF i ∉ Set.Ici s2 →
      (gramL_isSymmetric W).eigenvalues hF i = 0)
    (hWR : ∀ i, (gramR_isSymmetric W).eigenvalues hE i ∉ Set.Ici s2 →
      (gramR_isSymmetric W).eigenvalues hE i = 0) :
    hs bE (Ptop hF C τ ∘ₗ C - W - ((C - W) - Pbot hF W s2 ∘ₗ (C - W) ∘ₗ Qbot hE W s2)) ≤
      opn (gramL W - gramL C) / (s2 - τ) * (opn (gramR W - gramR C) / (s2 - τ)) * hs bE W +
      (opn (gramL W - gramL C) / (s2 - τ) + opn (gramL W - gramL C) / τ +
        (opn (gramR W - gramR C) / (s2 - τ) + opn (gramR W - gramR C) / τ)) * hs bE (C - W) := by
  have hs2 : 0 < s2 := hτ.trans hτs
  have hδ : 0 < s2 - τ := by linarith
  set D := C - W
  set hL := opn (gramL W - gramL C)
  set hR := opn (gramR W - gramR C)
  -- the four Davis–Kahan bounds
  have dkL1 : opn (Pbot hF C τ ∘ₗ Ptop hF W s2) ≤ hL / (s2 - τ) :=
    dk (gramL_isSymmetric W) (gramL_isSymmetric C) hF Set.ordConnected_Ici hδ (sep_top hτs.le)
  have dkR1 : opn (Qbot hE C τ ∘ₗ Qtop hE W s2) ≤ hR / (s2 - τ) :=
    dk (gramR_isSymmetric W) (gramR_isSymmetric C) hE Set.ordConnected_Ici hδ (sep_top hτs.le)
  have dkL2 : opn (Ptop hF C τ ∘ₗ Pbot hF W s2) ≤ hL / τ := by
    have := dk (gramL_isSymmetric W) (gramL_isSymmetric C) hF Set.ordConnected_Iic hτ (sep_bot hτ.le)
    simpa only [Pbot, Ptop, projL, bot_congr _ hF hs2 hWL] using this
  have dkR2 : opn (Qtop hE C τ ∘ₗ Qbot hE W s2) ≤ hR / τ := by
    have := dk (gramR_isSymmetric W) (gramR_isSymmetric C) hE Set.ordConnected_Iic hτ (sep_bot hτ.le)
    simpa only [Qbot, Qtop, projR, bot_congr _ hE hs2 hWR] using this
  -- symmetry of the projections
  have sPtW : (Ptop hF W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramL_isSymmetric W) hF (Set.Ici s2)
  have sPbW : (Pbot hF W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramL_isSymmetric W) hF (Set.Ici s2)ᶜ
  have sPtC : (Ptop hF C τ).IsSymmetric :=
    spectralProjection_isSymmetric (gramL_isSymmetric C) hF (Set.Ici τ)
  have sPbC : (Pbot hF C τ).IsSymmetric :=
    spectralProjection_isSymmetric (gramL_isSymmetric C) hF (Set.Ici τ)ᶜ
  have sQtW : (Qtop hE W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric W) hE (Set.Ici s2)
  have sQbW : (Qbot hE W s2).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric W) hE (Set.Ici s2)ᶜ
  have sQtC : (Qtop hE C τ).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric C) hE (Set.Ici τ)
  have sQbC : (Qbot hE C τ).IsSymmetric :=
    spectralProjection_isSymmetric (gramR_isSymmetric C) hE (Set.Ici τ)ᶜ
  -- differences of bottom projections
  have hPdiff : opn (Pbot hF C τ - Pbot hF W s2) ≤ hL / (s2 - τ) + hL / τ := by
    have e : Pbot hF C τ - Pbot hF W s2 =
        Ptop hF W s2 ∘ₗ Pbot hF C τ - Pbot hF W s2 ∘ₗ Ptop hF C τ := by
      ext y
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      have a1 := eq_sub_of_add_eq (Ptop_add_Pbot hF W s2 (Pbot hF C τ y))
      have a2 : Pbot hF W s2 (Ptop hF C τ y) = Pbot hF W s2 y - Pbot hF W s2 (Pbot hF C τ y) := by
        rw [← map_sub, ← eq_sub_of_add_eq (Ptop_add_Pbot hF C τ y)]
      rw [a1, a2]; abel
    rw [e]
    calc _ ≤ opn (Ptop hF W s2 ∘ₗ Pbot hF C τ) + opn (Pbot hF W s2 ∘ₗ Ptop hF C τ) := opn_sub_le _ _
      _ = opn (Pbot hF C τ ∘ₗ Ptop hF W s2) + opn (Ptop hF C τ ∘ₗ Pbot hF W s2) := by
        rw [opn_comp_swap sPtW sPbC, opn_comp_swap sPbW sPtC]
      _ ≤ _ := add_le_add dkL1 dkL2
  have hQdiff : opn (Qbot hE C τ - Qbot hE W s2) ≤ hR / (s2 - τ) + hR / τ := by
    have e : Qbot hE C τ - Qbot hE W s2 =
        Qtop hE W s2 ∘ₗ Qbot hE C τ - Qbot hE W s2 ∘ₗ Qtop hE C τ := by
      ext y
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      have a1 := eq_sub_of_add_eq (Qtop_add_Qbot hE W s2 (Qbot hE C τ y))
      have a2 : Qbot hE W s2 (Qtop hE C τ y) = Qbot hE W s2 y - Qbot hE W s2 (Qbot hE C τ y) := by
        rw [← map_sub, ← eq_sub_of_add_eq (Qtop_add_Qbot hE C τ y)]
      rw [a1, a2]; abel
    rw [e]
    calc _ ≤ opn (Qtop hE W s2 ∘ₗ Qbot hE C τ) + opn (Qbot hE W s2 ∘ₗ Qtop hE C τ) := opn_sub_le _ _
      _ = opn (Qbot hE C τ ∘ₗ Qtop hE W s2) + opn (Qtop hE C τ ∘ₗ Qbot hE W s2) := by
        rw [opn_comp_swap sQtW sQbC, opn_comp_swap sQbW sQtC]
      _ ≤ _ := add_le_add dkR1 dkR2
  -- the exact identity
  have hid : Ptop hF C τ ∘ₗ C - W - (D - Pbot hF W s2 ∘ₗ D ∘ₗ Qbot hE W s2) =
      -((Pbot hF C τ ∘ₗ Ptop hF W s2) ∘ₗ (W ∘ₗ (Qtop hE W s2 ∘ₗ Qbot hE C τ))) -
        (Pbot hF C τ - Pbot hF W s2) ∘ₗ (D ∘ₗ Qbot hE C τ) -
        Pbot hF W s2 ∘ₗ (D ∘ₗ (Qbot hE C τ - Qbot hE W s2)) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply, D]
    have A1 := eq_sub_of_add_eq (Ptop_add_Pbot hF C τ (C x))
    have A2 : Pbot hF C τ (C x) = Pbot hF C τ (C (Qbot hE C τ x)) := by
      rw [← Pbot_C hE hF, Pbot_idem]
    have A4 := W_eq_PWQ hE hF hWR (Qbot hE C τ x)
    rw [A1, A2]
    simp only [map_sub, A4]
    abel
  rw [hid]
  -- the three terms
  have hT1 : hs bE ((Pbot hF C τ ∘ₗ Ptop hF W s2) ∘ₗ (W ∘ₗ (Qtop hE W s2 ∘ₗ Qbot hE C τ))) ≤
      hL / (s2 - τ) * (hR / (s2 - τ)) * hs bE W := by
    have hU : opn (Qtop hE W s2 ∘ₗ Qbot hE C τ) ≤ hR / (s2 - τ) := by
      rw [opn_comp_swap sQtW sQbC]; exact dkR1
    calc _ ≤ opn (Pbot hF C τ ∘ₗ Ptop hF W s2) * hs bE (W ∘ₗ (Qtop hE W s2 ∘ₗ Qbot hE C τ)) :=
          hs_comp_left_le _ _ _
      _ ≤ hL / (s2 - τ) * (hs bE W * (hR / (s2 - τ))) :=
          mul_le_mul dkL1 ((hs_comp_right_le bE bF W _).trans
              (mul_le_mul_of_nonneg_left hU (hs_nonneg _ _))) (hs_nonneg _ _)
            (div_nonneg (opn_nonneg _) hδ.le)
      _ = _ := by ring
  have hT2 : hs bE ((Pbot hF C τ - Pbot hF W s2) ∘ₗ (D ∘ₗ Qbot hE C τ)) ≤
      (hL / (s2 - τ) + hL / τ) * hs bE D := by
    calc _ ≤ opn (Pbot hF C τ - Pbot hF W s2) * hs bE (D ∘ₗ Qbot hE C τ) := hs_comp_left_le _ _ _
      _ ≤ (hL / (s2 - τ) + hL / τ) * (hs bE D * 1) :=
          mul_le_mul hPdiff ((hs_comp_right_le bE bF D _).trans (mul_le_mul_of_nonneg_left
              (opn_spectralProjection_le (gramR_isSymmetric C) hE (Set.Ici τ)ᶜ) (hs_nonneg _ _))) (hs_nonneg _ _)
            (add_nonneg (div_nonneg (opn_nonneg _) hδ.le) (div_nonneg (opn_nonneg _) hτ.le))
      _ = _ := by ring
  have hT3 : hs bE (Pbot hF W s2 ∘ₗ (D ∘ₗ (Qbot hE C τ - Qbot hE W s2))) ≤
      (hR / (s2 - τ) + hR / τ) * hs bE D := by
    calc _ ≤ opn (Pbot hF W s2) * hs bE (D ∘ₗ (Qbot hE C τ - Qbot hE W s2)) := hs_comp_left_le _ _ _
      _ ≤ 1 * (hs bE D * (hR / (s2 - τ) + hR / τ)) :=
          mul_le_mul (opn_spectralProjection_le (gramL_isSymmetric W) hF (Set.Ici s2)ᶜ) ((hs_comp_right_le bE bF D _).trans
              (mul_le_mul_of_nonneg_left hQdiff (hs_nonneg _ _))) (hs_nonneg _ _) zero_le_one
      _ = _ := by ring
  have h1 := hs_sub_le bE
    (-((Pbot hF C τ ∘ₗ Ptop hF W s2) ∘ₗ (W ∘ₗ (Qtop hE W s2 ∘ₗ Qbot hE C τ))) -
      (Pbot hF C τ - Pbot hF W s2) ∘ₗ (D ∘ₗ Qbot hE C τ))
    (Pbot hF W s2 ∘ₗ (D ∘ₗ (Qbot hE C τ - Qbot hE W s2)))
  have h2 := hs_sub_le bE
    (-((Pbot hF C τ ∘ₗ Ptop hF W s2) ∘ₗ (W ∘ₗ (Qtop hE W s2 ∘ₗ Qbot hE C τ))))
    ((Pbot hF C τ - Pbot hF W s2) ∘ₗ (D ∘ₗ Qbot hE C τ))
  rw [hs_neg] at h2
  linarith

end Main

end OpenTheory.Perturbation
