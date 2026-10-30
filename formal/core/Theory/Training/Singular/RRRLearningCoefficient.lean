import Mathlib.Tactic

/-!
# The learning coefficient of reduced-rank regression exceeds the true dimension

Reduced-rank regression `y = B A x + noise` with `M` inputs, `N` outputs and `H`
hidden units, at a true parameter of rank `r`, has the Bayes learning coefficient
`λ(M,N,H,r)` of Aoyagi & Watanabe (2005), recorded here as `rlct8 = 8λ`. The
formula is cited, not derived. The rank-`r` matrices form a manifold of dimension
`r (M + N - r)`, so an estimator that selects the true rank has coefficient
`r (M + N - r) / 2`.

`rlct8_gain`: whenever the student is wider than the teacher (`r < H`) and the
teacher is not full rank (`r < min M N`), `λ ≥ r (M + N - r)/2 + 1/2`. So Bayes
with any prior of positive density at the truth is strictly worse, by at least
`1/(2n)`, than selecting the true rank.
-/

namespace OpenTheory.RRR

/-- `8λ` for reduced-rank regression (Aoyagi & Watanabe 2005, cited). -/
def rlct8 (M N H r : ℤ) : ℤ :=
  if N + r ≤ M + H ∧ M + r ≤ N + H ∧ H + r ≤ M + N then
    2 * (H + r) * (M + N) - (M - N) ^ 2 - (H + r) ^ 2 + (M + H + N + r) % 2
  else if M + H < N + r then 4 * (H * M - H * r + N * r)
  else if N + H < M + r then 4 * (H * N - H * r + M * r)
  else 4 * M * N

/-- **`λ` exceeds the true dimension by at least `1/2`.** -/
theorem rlct8_gain {M N H r : ℤ} (hrM : r < M) (hrN : r < N) (hrH : r < H) :
    4 * r * (M + N - r) + 4 ≤ rlct8 M N H r := by
  unfold rlct8
  split_ifs with h1 h2 h3
  · obtain ⟨hA, hB, hC⟩ := h1
    -- 8λ - 4r(M+N-r) = 2g(S-h) + g² - D² + parity, with g = H-r, h = H+r, S = M+N, D = M-N
    have key : 2 * (H + r) * (M + N) - (M - N) ^ 2 - (H + r) ^ 2 - 4 * r * (M + N - r) =
        2 * (H - r) * ((M + N) - (H + r)) + (H - r) ^ 2 - (M - N) ^ 2 := by ring
    have hpar : 0 ≤ (M + H + N + r) % 2 := Int.emod_nonneg _ (by norm_num)
    have hD : (M - N) ^ 2 ≤ (H - r) ^ 2 := by nlinarith
    rcases (show (M + N) - (H + r) = 0 ∨ (M + N) - (H + r) = 1 ∨ 2 ≤ (M + N) - (H + r) by omega)
      with h0 | h1' | h2'
    · -- S = h: g² - D² = (2N - 2r)(2M - 2r) ≥ 4
      have : (H - r) ^ 2 - (M - N) ^ 2 = (2 * N - 2 * r) * (2 * M - 2 * r) := by
        have : H - r = M + N - 2 * r := by linarith
        rw [this]; ring
      nlinarith
    · -- S = h + 1: the parity term is 1; if g = 1 then M - N is even, hence 0
      have hp1 : (M + H + N + r) % 2 = 1 := by omega
      rcases (show H - r = 1 ∨ 2 ≤ H - r by omega) with hg | hg
      · have hMN : M - N = 0 := by omega
        have hsq : (M - N) ^ 2 = 0 := by rw [hMN]; norm_num
        rw [h1', hg, hMN] at key
        norm_num at key
        rw [hp1]
        linarith
      · nlinarith
    · nlinarith
  · -- M + H < N + r: 8λ - 4r(M+N-r) = 4(H - r)(M - r)
    nlinarith [mul_pos (sub_pos.2 hrH) (sub_pos.2 hrM)]
  · nlinarith [mul_pos (sub_pos.2 hrH) (sub_pos.2 hrN)]
  · nlinarith [mul_pos (sub_pos.2 hrM) (sub_pos.2 hrN)]

end OpenTheory.RRR
