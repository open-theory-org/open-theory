/-! # Certificate decision procedures (core Lean only)

Each certificate type has a `Bool`-valued check written in plain `Nat` arithmetic, with no
import beyond Lean's core. The library proves once, with Mathlib, what a `true` result means
(`Specs.PoolRate`: `Claim.of_poolCheck`). A certificate is then checked by running the check:
compiled (`ot_check`, milliseconds, trusts the Lean compiler) or in the kernel (`by decide +kernel`
on a file importing only this module, about a second, trusts the kernel). Neither re-proves the
statistics.

* `popTree l x`: the set bits among the low `64 · 2ˡ` bits of `x`, by halving (depth `l`).
* `tailFast n k a b`: `bⁿ · P(Bin(n, a/b) ≤ k)` by Horner's rule, linear in `k`; it equals
  `BinomialTail.tailNumerator` (`PoolRate.tailFast_eq`).
* `poolCheck`: the `pool-rate` claim with the exact tail; `poolCheckWitness`: with a Chernoff
  witness `t = u/v`, one comparison whatever `k`.
-/

namespace OpenTheory.FastCheck

/-- Set bits among the low `f` bits of `w`. -/
def popWord : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, w => w % 2 + popWord f (w / 2)

/-- Set bits among the low `64 · 2ˡ` bits of `x`. -/
def popTree : Nat → Nat → Nat
  | 0, x => popWord 64 x
  | l + 1, x => popTree l (x % 2 ^ (64 * 2 ^ l)) + popTree l (x / 2 ^ (64 * 2 ^ l))

/-- Enough halving levels for `n` bits: `n ≤ 64 · 2^(levels n)`. -/
def levels (n : Nat) : Nat := Nat.log2 ((n + 63) / 64) + 1

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

/-- **`pool-rate` check, exact tail.** `x` packs the `n` sampled bits; at most `k` are set, and
`d · P(Bin(n, a/b) ≤ k) ≤ 1`. -/
def poolCheck (x n k a b d : Nat) : Bool :=
  decide (x < 2 ^ n) && decide (popTree (levels n) x ≤ k) && decide (a ≤ b) && decide (0 < b) &&
    decide (0 < d) && decide (d * tailFast n k a b ≤ b ^ n)

/-- **`pool-rate` check, Chernoff witness `t = u/v`.** -/
def poolCheckWitness (x n k a b u v d : Nat) : Bool :=
  decide (x < 2 ^ n) && decide (popTree (levels n) x ≤ k) && decide (a ≤ b) && decide (0 < b) &&
    decide (0 < u) && decide (u ≤ v) && decide (0 < d) &&
    decide (d * (b * v - a * v + a * u) ^ n * v ^ k ≤ (b * v) ^ n * u ^ k)

end OpenTheory.FastCheck
