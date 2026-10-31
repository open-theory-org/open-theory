import Checks.Bits

/-! # `pool-rate` decision procedures (core Lean only)

`poolCheck x n l k a b d`: the `n` sampled bits packed in `x` have at most `k` set, and
`d · P(Bin(n, a/b) ≤ k) ≤ 1`; `l` is the halving depth for the bit count, a witness checked
by `n ≤ 64 · 2ˡ`. `poolCheckWitness` replaces the exact tail by a Chernoff witness `t = u/v`,
one comparison whatever `k`. The tail is evaluated by Horner's rule, linear in `k`.

What `true` means is proved once in `Specs.PoolRate` (`Claim.of_poolCheck`,
`Claim.of_poolCheckWitness`); the tail equals `BinomialTail.tailNumerator` (`tailFast_eq`).
-/

namespace OpenTheory.Checks

/-- One Horner step for `Σᵢ C(n,i) aⁱ q^{k-i}`, on the state `(i, C(n,i), aⁱ, partial sum)`. -/
def hornerStep (n a q : Nat) : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | (i, c, p, s) => (i + 1, c * (n - i) / (i + 1), p * a, s * q + c * (n - i) / (i + 1) * (p * a))

/-- The state after `k` steps; its last component is `Σ_{i ≤ k} C(n,i) aⁱ q^{k-i}`. -/
def hornerState (n a q : Nat) : Nat → Nat × Nat × Nat × Nat
  | 0 => (0, 1, 1, 1)
  | k + 1 => hornerStep n a q (hornerState n a q k)

/-- `bⁿ · P(Bin(n, a/b) ≤ k)` for `a ≤ b`, in `O(k)` big-number operations. -/
def tailFast (n k a b : Nat) : Nat :=
  if n ≤ k then b ^ n else (b - a) ^ (n - k) * (hornerState n a (b - a) k).2.2.2

/-- **`pool-rate` check, exact tail.** -/
def poolCheck (x n l k a b d : Nat) : Bool :=
  (x >>> n == 0) && decide (n ≤ 64 <<< l) && decide (popTree l x ≤ k) && decide (a ≤ b) &&
    decide (0 < b) && decide (0 < d) && decide (d * tailFast n k a b ≤ b ^ n)

/-- **`pool-rate` check, Chernoff witness `t = u/v`.** -/
def poolCheckWitness (x n l k a b u v d : Nat) : Bool :=
  (x >>> n == 0) && decide (n ≤ 64 <<< l) && decide (popTree l x ≤ k) && decide (a ≤ b) &&
    decide (0 < b) && decide (0 < u) && decide (u ≤ v) && decide (0 < d) &&
    decide (d * (b * v - a * v + a * u) ^ n * v ^ k ≤ (b * v) ^ n * u ^ k)

end OpenTheory.Checks
