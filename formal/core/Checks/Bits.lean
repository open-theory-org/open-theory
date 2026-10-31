/-! # Bit counting for certificate checks (core Lean only)

`popTree l x` counts the set bits among the low `64 · 2ˡ` bits of `x` by halving: depth `l`,
then `popWord 64` on each 64-bit leaf. Powers of two are shifts. What it computes is proved in
`Specs.PoolRate` (`popTree_eq`).
-/

namespace OpenTheory.Checks

/-- Set bits among the low `f` bits of `w`. -/
def popWord : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, w => w % 2 + popWord f (w >>> 1)

/-- Set bits among the low `64 · 2ˡ` bits of `x`. -/
def popTree : Nat → Nat → Nat
  | 0, x => popWord 64 x
  | l + 1, x => popTree l (x % (1 <<< (64 <<< l))) + popTree l (x >>> (64 <<< l))

end OpenTheory.Checks
