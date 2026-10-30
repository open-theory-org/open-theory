import Theory.Training.Singular.PlateauModes
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic

/-!
# Mode decoupling: gradient flow of a two-layer linear network

Gradient flow of `L(A, B) = ½‖B A - C‖²` for `A : H × M`, `B : N × H` is
`Ȧ = Bᵀ (C - B A)`, `Ḃ = (C - B A) Aᵀ` (`gradField`). In the basis of singular
vectors of the data, `C` is diagonal with entries `σ i`. From the aligned,
balanced initialization `A(0) = ε·I`, `B(0) = ε·I`, with `H ≤ M`, `H ≤ N` and
`ε² < σ i`, **every** solution satisfies (`flow_decouples`)

  `(B A)(t) i j = if i = j and i < H then mode (σ i) ε t else 0`,

where `mode` is the logistic of `OpenTheory.Plateau`. So the network product
evolves mode by mode, and `OpenTheory.Plateau.plateau` applies to it.

The proof builds the explicit diagonal solution (`diagSol`, `diagSol_solves`)
and shows uniqueness for a smooth vector field from compactness
(`unique_of_contDiff`): any two solutions on `[0, T]` stay in a closed ball, on
which the field is Lipschitz.
-/

noncomputable section
open Set Real Filter Topology

namespace OpenTheory.Plateau

/-! ### Uniqueness for smooth autonomous ODEs -/

/-- Two solutions of `ẋ = v x` on `[a, b]` with the same initial value agree, when
`v` is `C¹` on a finite-dimensional space. No a priori bound is needed: both
solutions are bounded on the compact interval. -/
theorem unique_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {v : E → E} (hv : ContDiff ℝ 1 v) {f g : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  obtain ⟨Rf, hRf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Rg, hRg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  set R := max Rf Rg
  obtain ⟨K, hK⟩ := (hv.contDiffOn (s := Metric.closedBall (0 : E) R)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ODE_solution_unique_of_mem_Icc_right (s := fun _ => Metric.closedBall 0 R)
    (fun _ _ => hK) hf hf' (fun t ht => ?_) hg hg' (fun t ht => ?_) ha
  · exact mem_closedBall_zero_iff.2 ((hRf t (Ico_subset_Icc_self ht)).trans (le_max_left _ _))
  · exact mem_closedBall_zero_iff.2 ((hRg t (Ico_subset_Icc_self ht)).trans (le_max_right _ _))

/-! ### The gradient flow -/

variable {M N H : ℕ}

/-- The state `(A, B)`. -/
abbrev State (M N H : ℕ) := (Fin H → Fin M → ℝ) × (Fin N → Fin H → ℝ)

/-- The network product `(B A) i j`. -/
def prodBA (p : State M N H) (i : Fin N) (j : Fin M) : ℝ := ∑ l, p.2 i l * p.1 l j

/-- Gradient-flow field of `½‖B A - C‖²`, entrywise: `Ȧ = Bᵀ (C - B A)`, `Ḃ = (C - B A) Aᵀ`. -/
def gradField (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) : State M N H :=
  (fun k j => ∑ i, p.2 i k * (C i j - prodBA p i j),
   fun i k => ∑ j, (C i j - prodBA p i j) * p.1 k j)

/-- The same field in matrix notation. -/
theorem gradField_eq_matrix (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    gradField C p =
      (Matrix.transpose (Matrix.of p.2) * (C - Matrix.of p.2 * Matrix.of p.1),
        (C - Matrix.of p.2 * Matrix.of p.1) * Matrix.transpose (Matrix.of p.1)) := by
  ext k j <;> simp [gradField, prodBA, Matrix.mul_apply]

theorem gradField_contDiff (C : Matrix (Fin N) (Fin M) ℝ) :
    ContDiff ℝ 1 (gradField (H := H) C) := by
  refine ContDiff.prodMk ?_ ?_ <;>
  · refine contDiff_pi.2 fun k => contDiff_pi.2 fun j => ?_
    simp only [prodBA]
    fun_prop

/-! ### The explicit diagonal solution -/

/-- Diagonal data: `C i j = σ i` if `i = j`, else `0`. -/
def diagData (σ : ℕ → ℝ) : Matrix (Fin N) (Fin M) ℝ := fun i j => if (i : ℕ) = j then σ i else 0

/-- Amplitude of mode `k`: `√(mode (σ k) ε t)`, the common value of `a_k = b_k`. -/
def amp (σ : ℕ → ℝ) (ε t : ℝ) (k : ℕ) : ℝ := √(mode (σ k) ε t)

/-- The diagonal candidate: `A k j = δ_{kj} a_k`, `B i k = δ_{ik} a_k`. -/
def diagSol (σ : ℕ → ℝ) (ε : ℝ) (t : ℝ) : State M N H :=
  (fun k j => if (k : ℕ) = j then amp σ ε t k else 0,
   fun i k => if (i : ℕ) = k then amp σ ε t k else 0)

variable {σ : ℕ → ℝ} {ε : ℝ}

theorem mode_pos (hε : 0 < ε) (h : ε ^ 2 < σ') (t : ℝ) : 0 < mode σ' ε t := by
  have hσ : 0 < σ' := lt_of_le_of_lt (by positivity) h
  exact div_pos hσ (lt_of_lt_of_le one_pos (denom_ge_one hε h t))

theorem amp_sq (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) (t : ℝ) (k : ℕ) :
    amp σ ε t k * amp σ ε t k = mode (σ k) ε t :=
  mul_self_sqrt (mode_pos hε (hσ k) t).le

/-- `ȧ = a (σ - a²)`. -/
theorem hasDerivAt_amp (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) (t : ℝ) (k : ℕ) :
    HasDerivAt (fun t => amp σ ε t k)
      (amp σ ε t k * (σ k - amp σ ε t k * amp σ ε t k)) t := by
  have hpos := mode_pos hε (hσ k) t
  have := (hasDerivAt_mode hε (hσ k) t).sqrt hpos.ne'
  show HasDerivAt (fun y => √(mode (σ k) ε y)) _ t
  convert this using 1
  rw [amp_sq hε hσ, amp]
  have hs : 0 < √(mode (σ k) ε t) := sqrt_pos.2 hpos
  field_simp
  rw [sq_sqrt hpos.le]

/-- The product `B A` of the candidate. -/
theorem diagSol_prod (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) (t : ℝ)
    (i : Fin N) (j : Fin M) :
    prodBA (diagSol (M := M) (N := N) (H := H) σ ε t) i j =
      if (i : ℕ) = j ∧ (i : ℕ) < H then mode (σ i) ε t else 0 := by
  simp only [prodBA, diagSol]
  by_cases hiH : (i : ℕ) < H
  · rw [Finset.sum_eq_single ⟨i, hiH⟩]
    · by_cases hij : (i : ℕ) = j
      · have hjH : (j : ℕ) < H := hij ▸ hiH
        simp only [hij, hjH, true_and, ↓reduceIte]
        exact amp_sq hε hσ t j
      · simp only [hij, false_and, ↓reduceIte, mul_zero]
    · intro l _ hl
      have : (i : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
      simp only [this, ↓reduceIte, zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hiH]
    · intro l _
      have : (i : ℕ) ≠ l := fun h => hiH (h ▸ l.isLt)
      simp [this]


/-- The aligned, balanced initialization `A(0) = ε I`, `B(0) = ε I`. -/
def initState (ε : ℝ) : State M N H :=
  (fun k j => if (k : ℕ) = j then ε else 0, fun i k => if (i : ℕ) = k then ε else 0)

theorem amp_zero (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) (k : ℕ) : amp σ ε 0 k = ε := by
  have hσk : σ k ≠ 0 := (lt_of_le_of_lt (by positivity) (hσ k)).ne'
  rw [amp, mode_zero hε.ne' hσk, sqrt_sq hε.le]

theorem diagSol_zero (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) :
    diagSol (M := M) (N := N) (H := H) σ ε 0 = initState ε := by
  simp only [diagSol, initState, amp_zero hε hσ]

theorem diagSol_fst (t : ℝ) (k : Fin H) (j : Fin M) :
    (diagSol (M := M) (N := N) (H := H) σ ε t).1 k j = if (k : ℕ) = j then amp σ ε t k else 0 :=
  rfl

theorem diagSol_snd (t : ℝ) (i : Fin N) (k : Fin H) :
    (diagSol (M := M) (N := N) (H := H) σ ε t).2 i k = if (i : ℕ) = k then amp σ ε t k else 0 :=
  rfl

/-- **The diagonal candidate solves the gradient flow.** -/
theorem diagSol_solves (hHM : H ≤ M) (hHN : H ≤ N) (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i)
    (t : ℝ) :
    HasDerivAt (diagSol (M := M) (N := N) (H := H) σ ε)
      (gradField (diagData σ) (diagSol σ ε t)) t := by
  have hd := hasDerivAt_amp hε hσ t
  refine HasDerivAt.prodMk ?_ ?_
  · refine hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_
    have hkN : (k : ℕ) < N := lt_of_lt_of_le k.isLt hHN
    simp only [diagSol_snd]
    rw [Finset.sum_eq_single ⟨k, hkN⟩]
    · rw [diagSol_prod hε hσ]
      by_cases hkj : (k : ℕ) = j
      · have hc : ((⟨k, hkN⟩ : Fin N) : ℕ) = j ∧ ((⟨k, hkN⟩ : Fin N) : ℕ) < H := ⟨hkj, k.isLt⟩
        have hC : diagData σ ⟨k, hkN⟩ j = σ k := by simp [diagData, hkj]
        have hfun : (fun x => if (k : ℕ) = j then amp σ ε x k else 0) = fun x => amp σ ε x k := by
          funext x; simp [hkj]
        simp only [hc, hC, hfun, ↓reduceIte]
        rw [ite_eq_left (show (k : ℕ) = j ∧ True from ⟨hkj, trivial⟩), ← amp_sq hε hσ t k]
        exact hd k
      · have hC : diagData σ ⟨k, hkN⟩ j = 0 := by simp [diagData, hkj]
        simp only [hC, hkj, ↓reduceIte]
        convert hasDerivAt_const t (0 : ℝ) using 1
        simp
    · intro i _ hi
      have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun k => ?_
    have hkM : (k : ℕ) < M := lt_of_lt_of_le k.isLt hHM
    simp only [diagSol_fst]
    rw [Finset.sum_eq_single ⟨k, hkM⟩]
    · rw [diagSol_prod hε hσ]
      by_cases hik : (i : ℕ) = k
      · have hc : (i : ℕ) = ((⟨k, hkM⟩ : Fin M) : ℕ) ∧ (i : ℕ) < H := ⟨hik, hik ▸ k.isLt⟩
        have hC : diagData σ i ⟨k, hkM⟩ = σ k := by simp [diagData, hik]
        simp only [hc, hC, ↓reduceIte]
        convert hd k using 1
        simp only [true_and, k.isLt, ↓reduceIte]
        rw [← amp_sq hε hσ t k]
        ring
      · have hC : diagData σ i ⟨k, hkM⟩ = 0 := by simp [diagData, hik]
        simp only [hC, hik, ↓reduceIte]
        convert hasDerivAt_const t (0 : ℝ) using 1
        simp
    · intro j _ hj
      have : (k : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
      simp [this]
    · simp

/-- The hypotheses of `flow_decouples` are satisfiable: a solution from `ε I` exists. -/
theorem flow_exists (hHM : H ≤ M) (hHN : H ≤ N) (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i) :
    ∃ f : ℝ → State M N H, f 0 = initState ε ∧
      ∀ t, HasDerivAt f (gradField (diagData σ) (f t)) t :=
  ⟨diagSol σ ε, diagSol_zero hε hσ, diagSol_solves hHM hHN hε hσ⟩

/-- **Mode decoupling.** Every gradient-flow trajectory from the aligned, balanced
initialization `ε I` on diagonal data has network product
`(B A)(t) i j = if i = j and i < H then mode (σ i) ε t else 0`. -/
theorem flow_decouples (hHM : H ≤ M) (hHN : H ≤ N) (hε : 0 < ε) (hσ : ∀ i, ε ^ 2 < σ i)
    {T : ℝ} {f : ℝ → State M N H} (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (gradField (diagData σ) (f t)) (Ici t) t)
    (h0 : f 0 = initState ε) :
    ∀ t ∈ Icc 0 T, ∀ i j,
      prodBA (f t) i j = if (i : ℕ) = j ∧ (i : ℕ) < H then mode (σ i) ε t else 0 := by
  have hg : ∀ t, HasDerivAt (diagSol (M := M) (N := N) (H := H) σ ε)
      (gradField (diagData σ) (diagSol σ ε t)) t := diagSol_solves hHM hHN hε hσ
  have heq := unique_of_contDiff (gradField_contDiff (diagData σ)) hf hf'
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => (hg t).hasDerivWithinAt)
    (h0.trans (diagSol_zero hε hσ).symm)
  intro t ht i j
  rw [heq ht, diagSol_prod hε hσ]

/-- **The plateau for the network product.** Fix diagonal data with singular values
`σ i ≥ σmin > 0`, and classify the first `H` modes as signal (`σ k c₁ > 1`) or noise
(`σ k c₂ < 1`). For every `δ > 0` and all small `ε > 0`, every gradient-flow
trajectory from `ε I` that runs past `c₂ log (1/ε)` has, on the window
`[c₁ log (1/ε), c₂ log (1/ε)]`, every entry of `B A` within `δ` of the best fit
keeping exactly the signal modes. -/
theorem flow_plateau (hHM : H ≤ M) (hHN : H ≤ N) {σmin : ℝ} (hmin : 0 < σmin)
    (hσ : ∀ i, σmin ≤ σ i) {c₁ c₂ : ℝ} (signal : Fin H → Prop) [DecidablePred signal]
    (hsig : ∀ k, signal k → 1 < σ k * c₁) (hnoise : ∀ k, ¬ signal k → σ k * c₂ < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (T : ℝ) (f : ℝ → State M N H), ContinuousOn f (Icc 0 T) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt f (gradField (diagData σ) (f t)) (Ici t) t) →
      f 0 = initState ε →
      ∀ t ∈ Icc (c₁ * log (1 / ε)) (c₂ * log (1 / ε)), 0 ≤ t → t ≤ T → ∀ i j,
        |prodBA (f t) i j -
          (if h : (i : ℕ) = j ∧ (i : ℕ) < H then (if signal ⟨i, h.2⟩ then σ i else 0) else 0)| < δ := by
  have hpl := plateau (σ := fun k : Fin H => σ k) (fun k => lt_of_lt_of_le hmin (hσ k)) signal
    hsig hnoise hδ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ^ 2 < σmin := by
    have : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
    have h2 := (this.eventually (gt_mem_nhds (by simpa using hmin))).filter_mono
      (nhdsWithin_le_nhds (s := Ioi 0))
    filter_upwards [h2, self_mem_nhdsWithin] with ε h hε using ⟨hε, h⟩
  filter_upwards [hpl, hsmall] with ε hε ⟨hεpos, hεσ⟩ T f hf hf' h0 t ht ht0 htT i j
  have hσ' : ∀ i, ε ^ 2 < σ i := fun i => lt_of_lt_of_le hεσ (hσ i)
  rw [flow_decouples hHM hHN hεpos hσ' hf hf' h0 t ⟨ht0, htT⟩ i j]
  split_ifs with h1 hsg
  · obtain ⟨hs, _⟩ := hε t ht ⟨i, h1.2⟩
    rw [abs_sub_comm]; exact hs hsg
  · obtain ⟨_, hn⟩ := hε t ht ⟨i, h1.2⟩
    rw [sub_zero]; exact hn hsg
  · simpa using hδ

/-! ### Invariance under orthogonal changes of basis -/

/-- Rotating outputs by `Uᵀ` and inputs by `V`: `(A, B) ↦ (A V, Uᵀ B)`. -/
def rotate (U : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin M) (Fin M) ℝ) (p : State M N H) :
    State M N H :=
  (Matrix.of p.1 * V, Matrix.transpose U * Matrix.of p.2)

/-- **Orthogonal invariance of the field.** If `U Uᵀ = I` and `V Vᵀ = I`, the field for
the rotated data `Uᵀ C V` at the rotated state is the rotated field. -/
theorem gradField_rotate {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Matrix.transpose U = 1) (hV : V * Matrix.transpose V = 1)
    (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    gradField (Matrix.transpose U * C * V) (rotate U V p) = rotate U V (gradField C p) := by
  set A : Matrix (Fin H) (Fin M) ℝ := Matrix.of p.1
  set B : Matrix (Fin N) (Fin H) ℝ := Matrix.of p.2
  have hBA : (Matrix.transpose U * B) * (A * V) = Matrix.transpose U * (B * A) * V := by
    simp only [Matrix.mul_assoc]
  have hr : Matrix.transpose U * C * V - Matrix.transpose U * (B * A) * V =
      Matrix.transpose U * (C - B * A) * V := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [gradField_eq_matrix, gradField_eq_matrix]
  refine Prod.ext ?_ ?_
  · show Matrix.transpose (Matrix.transpose U * B) *
        (Matrix.transpose U * C * V - (Matrix.transpose U * B) * (A * V)) =
      (Matrix.transpose B * (C - B * A)) * V
    rw [hBA, hr, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hU, Matrix.one_mul]
  · show (Matrix.transpose U * C * V - (Matrix.transpose U * B) * (A * V)) *
        Matrix.transpose (A * V) = Matrix.transpose U * ((C - B * A) * Matrix.transpose A)
    rw [hBA, hr, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]

/-- **Solutions rotate to solutions.** A gradient-flow trajectory for data `C` is mapped
by `rotate U V` to a trajectory for `Uᵀ C V`. With an SVD `C = U Σ Vᵀ`, this reduces
the general case to diagonal data, where `flow_decouples` applies. -/
theorem rotate_solves {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Matrix.transpose U = 1) (hV : V * Matrix.transpose V = 1)
    (C : Matrix (Fin N) (Fin M) ℝ) {f : ℝ → State M N H} {t : ℝ}
    (hf : HasDerivAt f (gradField C (f t)) t) :
    HasDerivAt (fun s => rotate U V (f s))
      (gradField (Matrix.transpose U * C * V) (rotate U V (f t))) t := by
  rw [gradField_rotate hU hV]
  -- `rotate U V` is a continuous linear map
  let Llin : State M N H →ₗ[ℝ] State M N H :=
    { toFun := rotate U V
      map_add' := fun p q => by
        simp only [rotate, Prod.fst_add, Prod.snd_add]
        congr 1
        · exact Matrix.add_mul (Matrix.of p.1) (Matrix.of q.1) V
        · exact Matrix.mul_add (Matrix.transpose U) (Matrix.of p.2) (Matrix.of q.2)
      map_smul' := fun c p => by
        simp only [rotate, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
        congr 1
        · exact Matrix.smul_mul c (Matrix.of p.1) V
        · exact Matrix.mul_smul (Matrix.transpose U) c (Matrix.of p.2) }
  let L : State M N H →L[ℝ] State M N H := LinearMap.toContinuousLinearMap Llin
  exact L.hasFDerivAt.comp_hasDerivAt t hf

end OpenTheory.Plateau
