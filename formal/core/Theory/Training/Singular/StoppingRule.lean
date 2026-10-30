import Theory.Training.Singular.PlateauEstimator

/-!
# A data-driven stopping rule that provably lands on the plateau

The rule uses only the training-loss curve `L(t) = ½‖C - B A‖²_F`: let `t̂` be the first
time with `L(t) ≤ ρ` (`hitTime`), and stop at `(3/2) t̂`.

`stopping_rule`: on the good event (`‖C Cᵀ - W Wᵀ‖ ≤ h` with `h ≤ s2/8` and `N h < ρ ≤ s2/4`),
for gradient flow from the aligned start `ε`, the stopped network converges, as `ε → 0`,
to the truncated SVD `trunc (s2/2) C`, the estimator whose risk is `r (M + N - r)`.

Why: before the weakest signal mode `σ*` switches on (`t < 0.9 log(1/ε)/σ*`), the loss is at
least `½(7σ*/8)² > ρ`; once all signal modes are on and the noise modes still off
(`t = 1.1 log(1/ε)/σ*`), the loss is at most `½ N (√h + η)² < ρ`. So
`(3/2) t̂ ∈ [1.35, 1.65] · log(1/ε)/σ*`, inside the plateau window, because noise singular
values are below `σ*/√7`.
-/

noncomputable section
open Set Real Filter Topology Matrix
open scoped RealInnerProductSpace
open OpenTheory.HilbertSchmidt OpenTheory.RankTruncation OpenTheory.Perturbation
  OpenTheory.TruncationRisk OpenTheory.TruncationRank OpenTheory.TruncationEvent

namespace OpenTheory.Plateau

variable {M N H : ℕ}

/-- The training loss `½ ‖C - B A‖²_F`. -/
def trainLoss (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, (C i j - prodBA p i j) ^ 2

/-- The first time the training loss is at most `ρ`. -/
def hitTime (C : Matrix (Fin N) (Fin M) ℝ) (f : ℝ → State M N H) (ρ : ℝ) : ℝ :=
  sInf {t | 0 ≤ t ∧ trainLoss C (f t) ≤ ρ}

theorem sum_sq_eq_trace (X : Matrix (Fin N) (Fin M) ℝ) :
    ∑ i, ∑ j, X i j ^ 2 = (X * Xᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

theorem sum_sq_conj {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (X : Matrix (Fin N) (Fin M) ℝ) :
    ∑ i, ∑ j, (Uᵀ * X * V) i j ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  rw [sum_sq_eq_trace, sum_sq_eq_trace]
  have e : Uᵀ * X * V * (Uᵀ * X * V)ᵀ = Uᵀ * (X * Xᵀ) * U := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem prodBA_rotate (U : Matrix (Fin N) (Fin N) ℝ) (V : Matrix (Fin M) (Fin M) ℝ)
    (p : State M N H) : Matrix.of (prodBA (rotate U V p)) = Uᵀ * Matrix.of (prodBA p) * V := by
  rw [of_prodBA, of_prodBA]
  show (Uᵀ * Matrix.of p.2) * (Matrix.of p.1 * V) = _
  simp only [Matrix.mul_assoc]

/-- The training loss is invariant under rotating data and state together. -/
theorem trainLoss_rotate {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) :
    trainLoss (Uᵀ * C * V) (rotate U V p) = trainLoss C p := by
  unfold trainLoss
  congr 1
  have hm : Uᵀ * C * V - Matrix.of (prodBA (rotate U V p)) =
      Uᵀ * (C - Matrix.of (prodBA p)) * V := by
    rw [prodBA_rotate, Matrix.mul_sub, Matrix.sub_mul]
  have he : ∀ i j, (Uᵀ * C * V) i j - prodBA (rotate U V p) i j =
      (Uᵀ * (C - Matrix.of (prodBA p)) * V) i j := fun i j => by
    rw [← hm]; rfl
  simp_rw [he]
  rw [sum_sq_conj hU hV]
  rfl

theorem trainLoss_ge (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) (i : Fin N) (j : Fin M) :
    (1 / 2) * (C i j - prodBA p i j) ^ 2 ≤ trainLoss C p := by
  unfold trainLoss
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => (C i j - prodBA p i j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)

/-- Loss bound for a residual supported on the diagonal. -/
theorem trainLoss_le_of_diag (C : Matrix (Fin N) (Fin M) ℝ) (p : State M N H) {B : ℝ}
    (hB : 0 ≤ B) (hoff : ∀ (i : Fin N) (j : Fin M), (i : ℕ) ≠ j → C i j - prodBA p i j = 0)
    (hdiag : ∀ (i : Fin N) (j : Fin M), (i : ℕ) = j → (C i j - prodBA p i j) ^ 2 ≤ B) :
    trainLoss C p ≤ (1 / 2) * (N * B) := by
  classical
  unfold trainLoss
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hrow : ∀ i : Fin N, ∑ j, (C i j - prodBA p i j) ^ 2 ≤ B := by
    intro i
    calc ∑ j, (C i j - prodBA p i j) ^ 2 ≤ ∑ j : Fin M, (if (i : ℕ) = j then B else 0) := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases h : (i : ℕ) = j
          · rw [ite_eq_left h]; exact hdiag i j h
          · rw [ite_eq_right h, hoff i j h]; simp
      _ = (Finset.univ.filter fun j : Fin M => (i : ℕ) = j).card • B := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      _ ≤ 1 • B := by
          refine nsmul_le_nsmul_left hB (Finset.card_le_one.2 fun a ha b hb => ?_)
          simp only [Finset.mem_filter] at ha hb
          exact Fin.ext (ha.2.symm.trans hb.2)
      _ = B := one_nsmul B
  calc ∑ i, ∑ j, (C i j - prodBA p i j) ^ 2 ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hrow i
    _ = N * B := by simp

/-- **The stopping rule lands on the plateau.** Stop at `(3/2) t̂`, where `t̂` is the first
time the training loss drops below `ρ`. On the good event, as `ε → 0`, the stopped network
converges to the truncated SVD `trunc (s2/2) C`. -/
theorem stopping_rule (hHM : H ≤ M) (hHN : H ≤ N) {C W : Matrix (Fin N) (Fin M) ℝ}
    {U : Matrix (Fin N) (Fin N) ℝ} {V : Matrix (Fin M) (Fin M) ℝ} {σ : ℕ → ℝ}
    (hU : U * Uᵀ = 1) (hV : V * Vᵀ = 1) (hsvd : Uᵀ * C * V = diagData σ)
    (hanti : Antitone σ) {σmin : ℝ} (hmin : 0 < σmin) (hσ : ∀ k, σmin ≤ σ k)
    {s2 h ρ : ℝ} (hs2 : 0 < s2) (hh0 : 0 ≤ h) (hh : h ≤ s2 / 8)
    (hWL : ∀ i, (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i ∉ Set.Ici s2 →
      (gramL_isSymmetric (toEuclideanLin W)).eigenvalues finrank_EN i = 0)
    (hclose : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ h)
    (hrH : countIn (gramL_isSymmetric (toEuclideanLin W)) finrank_EN (Set.Ici s2) ≤ H)
    (hρ1 : N * h < ρ) (hρ2 : ρ ≤ s2 / 4) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ f : ℝ → State M N H, (∀ t, HasDerivAt f (gradField C (f t)) t) →
      rotate U V (f 0) = initState ε → ∀ i j,
        |prodBA (f (3 / 2 * hitTime C f ρ)) i j -
          toEuclideanLin.symm (trunc finrank_EN (toEuclideanLin C) (s2 / 2)) i j| < δ := by
  classical
  have hpos : ∀ k, 0 < σ k := fun k => hmin.trans_le (hσ k)
  have hclose4 : opn (gramL (toEuclideanLin C) - gramL (toEuclideanLin W)) ≤ s2 / 4 :=
    hclose.trans (by linarith)
  -- classification of the singular values
  have hsplit : ∀ k : ℕ, k < N → k < M →
      (s2 / 2 ≤ σ k ^ 2 → s2 - h ≤ σ k ^ 2) ∧ (σ k ^ 2 < s2 / 2 → σ k ^ 2 ≤ h) := by
    intro k hkN hkM
    have hev : ev (M := M) σ (⟨k, hkN⟩ : Fin N) = σ k ^ 2 := by simp [ev, hkM]
    have heig := gramL_col hU hV hsvd (⟨k, hkN⟩ : Fin N)
    rw [hev] at heig
    exact eigenvalue_split finrank_EN hWL hclose (by linarith) (by linarith)
      ((orthonormal_col hU).ne_zero _) heig
  have hnoiseLe : ∀ k : ℕ, k < N → k < M → (k < H → σ k ^ 2 < s2 / 2) → σ k ≤ √h := by
    intro k hkN hkM hk
    have hsq : σ k ^ 2 ≤ h := by
      by_cases hkH : k < H
      · exact (hsplit k hkN hkM).2 (hk hkH)
      · exact (hsplit k hkN hkM).2 (sq_lt_of_ge hU hV hsvd hanti hpos hs2 hWL hclose4 hrH
          hkN hkM (not_lt.1 hkH))
    rw [← Real.sqrt_sq (hpos k).le]; exact Real.sqrt_le_sqrt hsq
  let signal : Fin H → Prop := fun k => s2 / 2 ≤ σ k ^ 2
  -- the loss threshold margin
  set ηL := min 1 ((ρ - N * h) / ((N + 1) * (2 * √h + 1)))
  have hηL : 0 < ηL := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hρpos : 0 < ρ := lt_of_le_of_lt (by positivity) hρ1
  have hloss_small : ∀ η, 0 ≤ η → η ≤ ηL → (1 / 2) * (N * (√h + η) ^ 2) < ρ := by
    intro η hη0 hη
    have h2 : η * ((N + 1) * (2 * √h + 1)) ≤ ρ - N * h := by
      have := hη.trans (min_le_right _ _); rwa [le_div_iff₀ (by positivity)] at this
    have hX : 0 ≤ η * (2 * √h + 1) := by positivity
    have hsq : (√h + η) ^ 2 ≤ h + η * (2 * √h + 1) := by
      have h1 : η ≤ 1 := hη.trans (min_le_left _ _)
      have := Real.sq_sqrt hh0; nlinarith [Real.sqrt_nonneg h]
    have hN : (N : ℝ) * (η * (2 * √h + 1)) ≤ ρ - N * h :=
      calc (N : ℝ) * (η * (2 * √h + 1)) ≤ (N + 1) * (η * (2 * √h + 1)) := by nlinarith
        _ = η * ((N + 1) * (2 * √h + 1)) := by ring
        _ ≤ _ := h2
    calc (1 / 2) * (N * (√h + η) ^ 2) ≤ (1 / 2) * (N * (h + η * (2 * √h + 1))) := by gcongr
      _ ≤ (1 / 2) * ρ := by nlinarith
      _ < ρ := by linarith
  -- residual bound in SVD coordinates, given the mode estimates at time `t`
  have hresid : ∀ (ε t η : ℝ) (p : State M N H), 0 ≤ η →
      (∀ i j, prodBA p i j = if (i : ℕ) = j ∧ (i : ℕ) < H then mode (σ i) ε t else 0) →
      (∀ k : Fin H, (signal k → |σ k - mode (σ k) ε t| < η) ∧ (¬ signal k → |mode (σ k) ε t| < η)) →
      trainLoss (diagData σ) p ≤ (1 / 2) * (N * (√h + η) ^ 2) := by
    intro ε t η p hη hp hmodes
    refine trainLoss_le_of_diag _ _ (sq_nonneg _) (fun i j hij => ?_) (fun i j hij => ?_)
    · rw [hp]; simp [diagData, hij]
    · rw [hp]
      simp only [diagData, hij, true_and, ite_true]
      have hjN : (j : ℕ) < N := hij ▸ i.2
      by_cases hjH : (j : ℕ) < H
      · rw [ite_eq_left hjH]
        obtain ⟨hs, hn⟩ := hmodes ⟨j, hjH⟩
        by_cases hsig : signal ⟨j, hjH⟩
        · have := hs hsig
          calc (σ j - mode (σ j) ε t) ^ 2 ≤ η ^ 2 := by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
            _ ≤ (√h + η) ^ 2 := pow_le_pow_left₀ hη (by linarith [Real.sqrt_nonneg h]) 2
        · have hm := hn hsig
          have hσj := hnoiseLe j hjN j.2 (fun _ => lt_of_not_ge hsig)
          rw [← sq_abs]
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          calc |σ j - mode (σ j) ε t| ≤ |σ j| + |mode (σ j) ε t| := abs_sub _ _
            _ ≤ √h + η := by rw [abs_of_pos (hpos j)]; linarith
      · rw [ite_eq_right hjH, sub_zero]
        have hσj := hnoiseLe j hjN j.2 (fun h' => absurd h' hjH)
        exact pow_le_pow_left₀ (hpos j).le (by linarith) 2
  -- common smallness of `ε`
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 ∧ ε ^ 2 < σmin := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ^ 2 < σmin := by
      have : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
      exact this.eventually (gt_mem_nhds (by simpa using hmin))
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := gt_mem_nhds one_pos
    filter_upwards [(h1.and h2).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      ε ⟨a, b⟩ c using ⟨c, b, a⟩
  -- the network product in SVD coordinates
  have hformula : ∀ ε, 0 < ε → ε ^ 2 < σmin → ∀ f : ℝ → State M N H,
      (∀ t, HasDerivAt f (gradField C (f t)) t) → rotate U V (f 0) = initState ε →
      ∀ t, 0 ≤ t → (trainLoss C (f t) = trainLoss (diagData σ) (rotate U V (f t)) ∧
        ∀ i j, prodBA (rotate U V (f t)) i j =
          if (i : ℕ) = j ∧ (i : ℕ) < H then mode (σ i) ε t else 0) := by
    intro ε hε hε2 f hf h0 t ht
    let g : ℝ → State M N H := fun s => rotate U V (f s)
    have hg : ∀ s, HasDerivAt g (gradField (diagData σ) (g s)) s := fun s => by
      have := rotate_solves hU hV C (hf s); rwa [hsvd] at this
    refine ⟨by rw [← hsvd, trainLoss_rotate hU hV], ?_⟩
    exact flow_decouples hHM hHN hε (fun i => lt_of_lt_of_le hε2 (hσ i)) (T := t) (f := g)
      (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => (hg s).hasDerivWithinAt)
      h0 t ⟨ht, le_rfl⟩
  have hL := plateauMatrix_eq hU hV hsvd hanti hpos hs2 hWL hclose4 hrH
  by_cases hS : ∃ k : Fin H, signal k
  · -- the weakest signal mode
    have hSne : (Finset.univ.filter signal).Nonempty := by
      obtain ⟨k, hk⟩ := hS; exact ⟨k, by simpa using hk⟩
    set σs := (Finset.univ.filter signal).inf' hSne (fun k => σ k)
    obtain ⟨ks, hks, hσks⟩ := Finset.exists_mem_eq_inf' hSne (fun k => σ k)
    replace hσks : σs = σ ks := hσks
    have hksig : signal ks := by simpa using hks
    have hσs_le : ∀ k, signal k → σs ≤ σ k := fun k hk =>
      Finset.inf'_le _ (by simpa using hk)
    have hσs_pos : 0 < σs := by rw [hσks]; exact hpos ks
    have hσs_sq : 7 * s2 / 8 ≤ σs ^ 2 := by
      have := (hsplit ks (lt_of_lt_of_le ks.2 hHN) (lt_of_lt_of_le ks.2 hHM)).1 hksig
      rw [hσks]; linarith
    have hnoise_sq : ∀ k : Fin H, ¬ signal k → σ k ^ 2 ≤ s2 / 8 := by
      intro k hk
      have := hnoiseLe k (lt_of_lt_of_le k.2 hHN) (lt_of_lt_of_le k.2 hHM)
        (fun _ => lt_of_not_ge hk)
      have h2 : σ k ^ 2 ≤ h := by
        rw [← Real.sq_sqrt hh0]; exact pow_le_pow_left₀ (hpos k).le this 2
      linarith
    -- ratio bound: (σ_k · c / σs)² < 1 for noise modes and c ≤ 33/20
    have hratio : ∀ k : Fin H, ¬ signal k → ∀ c, 0 < c → c ≤ 33 / 20 → σ k * (c / σs) < 1 := by
      intro k hk c hc0 hc
      have hsq : (σ k * (c / σs)) ^ 2 < 1 ^ 2 := by
        rw [mul_pow, div_pow, one_pow]
        have hσs2 : 0 < σs ^ 2 := by positivity
        rw [mul_div_assoc', div_lt_one hσs2]
        have hc2 : c ^ 2 ≤ (33 / 20) ^ 2 := pow_le_pow_left₀ hc0.le hc 2
        calc σ k ^ 2 * c ^ 2 ≤ (s2 / 8) * (33 / 20) ^ 2 :=
              mul_le_mul (hnoise_sq k hk) hc2 (sq_nonneg _) (by positivity)
          _ < 7 * s2 / 8 := by nlinarith
          _ ≤ σs ^ 2 := hσs_sq
      exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hsq
    have hsig_ratio : ∀ k, signal k → ∀ c, 1 < c → 1 < σ k * (c / σs) := by
      intro k hk c hc
      have := hσs_le k hk
      rw [mul_div_assoc', lt_div_iff₀ hσs_pos]
      nlinarith
    set η := min (σs / 8) ηL
    have hη : 0 < η := lt_min (by positivity) hηL
    -- the four eventual facts
    have E1 := rotated_plateau_window hHM hHN hU hV hsvd hmin hσ (c₁ := 27 / 20 / σs)
      (c₂ := 33 / 20 / σs) signal (fun k hk => hsig_ratio k hk _ (by norm_num))
      (fun k hk => hratio k hk _ (by norm_num) le_rfl) hδ
    have E2 := noise_off (hpos ks) (c₂ := 9 / 10 / σs)
      (by rw [hσks.symm, mul_div_assoc', div_lt_one hσs_pos]; linarith) hη
    have E3 := plateau (σ := fun k : Fin H => σ k) (fun k => hpos k) (c₁ := 11 / 10 / σs)
      (c₂ := 11 / 10 / σs) signal (fun k hk => hsig_ratio k hk _ (by norm_num))
      (fun k hk => hratio k hk _ (by norm_num) (by norm_num)) hη
    filter_upwards [E1, E2, E3, hsmall] with ε hE1 hE2 hE3 ⟨hε0, hε1, hε2⟩ f hf h0 i j
    have hlog : 0 ≤ log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
    set T := {t | 0 ≤ t ∧ trainLoss C (f t) ≤ ρ}
    -- an upper point
    set t₀ := 11 / 10 / σs * log (1 / ε)
    have ht₀ : 0 ≤ t₀ := mul_nonneg (by positivity) hlog
    have ht₀T : t₀ ∈ T := by
      refine ⟨ht₀, ?_⟩
      obtain ⟨hl, hp⟩ := hformula ε hε0 hε2 f hf h0 t₀ ht₀
      rw [hl]
      refine le_of_lt (lt_of_le_of_lt (hresid ε t₀ η _ hη.le hp ?_)
        (hloss_small η hη.le (min_le_right _ _)))
      exact fun k => hE3 t₀ ⟨le_rfl, le_rfl⟩ k
    have hbdd : BddBelow T := ⟨0, fun t ht => ht.1⟩
    have hup : hitTime C f ρ ≤ t₀ := csInf_le hbdd ht₀T
    -- a lower bound: before `0.9 log(1/ε)/σs` the weakest signal mode is still off
    have hlow : 9 / 10 / σs * log (1 / ε) ≤ hitTime C f ρ := by
      refine le_csInf ⟨t₀, ht₀T⟩ fun t ht => ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨hl, hp⟩ := hformula ε hε0 hε2 f hf h0 t ht.1
      have hm := hE2 t hlt.le
      have hksN : (ks : ℕ) < N := lt_of_lt_of_le ks.2 hHN
      have hksM : (ks : ℕ) < M := lt_of_lt_of_le ks.2 hHM
      have hge := trainLoss_ge (diagData σ) (rotate U V (f t)) ⟨ks, hksN⟩ ⟨ks, hksM⟩
      rw [hp] at hge
      simp only [diagData, true_and, ks.2, ite_true] at hge
      rw [← hl] at hge
      have hbig : 7 * σs / 8 ≤ σ ks - mode (σ ks) ε t := by
        have h1 := (abs_lt.1 hm).2
        have hηs : η ≤ σs / 8 := min_le_left _ _
        linarith [hσks]
      have : (1 / 2) * (7 * σs / 8) ^ 2 ≤ (1 / 2) * (σ ks - mode (σ ks) ε t) ^ 2 := by
        gcongr
      nlinarith [ht.2]
    -- the stopping time is inside the window
    have hstop : 3 / 2 * hitTime C f ρ ∈ Icc (27 / 20 / σs * log (1 / ε)) (33 / 20 / σs * log (1 / ε)) := by
      constructor
      · have : 27 / 20 / σs * log (1 / ε) = 3 / 2 * (9 / 10 / σs * log (1 / ε)) := by ring
        rw [this]; linarith
      · have : 33 / 20 / σs * log (1 / ε) = 3 / 2 * t₀ := by simp only [t₀]; ring
        rw [this]; linarith
    have hstop0 : 0 ≤ 3 / 2 * hitTime C f ρ :=
      le_trans (mul_nonneg (by positivity) hlog) hstop.1
    have key := hE1 f hf h0 _ hstop hstop0 i j
    rw [hL] at key
    rw [trunc_eq_svd hU hV hsvd, LinearEquiv.symm_apply_apply]
    exact key
  · -- no signal mode: the loss is already below `ρ` at time 0
    push Not at hS
    have E1 := rotated_plateau_window hHM hHN hU hV hsvd hmin hσ (c₁ := 0) (c₂ := 0) signal
      (fun k hk => absurd hk (by simpa using hS k)) (fun k _ => by simp) hδ
    have Eη : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 < ηL := by
      have : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
      exact (this.eventually (gt_mem_nhds (by simpa using hηL))).filter_mono nhdsWithin_le_nhds
    filter_upwards [E1, Eη, hsmall] with ε hE1 hεη ⟨hε0, hε1, hε2⟩ f hf h0 i j
    obtain ⟨hl, hp⟩ := hformula ε hε0 hε2 f hf h0 0 le_rfl
    have h0T : (0 : ℝ) ∈ {t | 0 ≤ t ∧ trainLoss C (f t) ≤ ρ} := by
      refine ⟨le_rfl, ?_⟩
      rw [hl]
      refine le_of_lt (lt_of_le_of_lt (hresid ε 0 ηL _ hηL.le hp ?_)
        (hloss_small _ hηL.le le_rfl))
      intro k
      refine ⟨fun hk => absurd hk (by simpa using hS k), fun _ => ?_⟩
      rw [mode_zero hε0.ne' (hpos k).ne', abs_of_nonneg (sq_nonneg _)]
      exact hεη
    have hbdd : BddBelow {t | 0 ≤ t ∧ trainLoss C (f t) ≤ ρ} := ⟨0, fun t ht => ht.1⟩
    have hhit : hitTime C f ρ = 0 :=
      le_antisymm (csInf_le hbdd h0T) (le_csInf ⟨0, h0T⟩ fun t ht => ht.1)
    have key := hE1 f hf h0 (3 / 2 * hitTime C f ρ) (by rw [hhit]; simp) (by rw [hhit]; simp) i j
    rw [hL] at key
    rw [trunc_eq_svd hU hV hsvd, LinearEquiv.symm_apply_apply]
    exact key

end OpenTheory.Plateau
