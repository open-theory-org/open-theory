import Checks.MLP
import Checks.PoolRate

/-!
# Registry of certificate checks

One entry per check, shared by both lanes so they cannot drift: `ot_check` calls `run`
(compiled), `ot_kernel` applies the constant named `const` to `prepare args` and has the kernel
evaluate it. `prepare` is untrusted: it only fills in witnesses that the check verifies.
-/

namespace OpenTheory.Checks

/-- How the kernel lane passes the (prepared) arguments to the constant. -/
inductive Shape where
  /-- `k` natural arguments. -/
  | nats (k : Nat)
  /-- `k` natural arguments, then one list of records: the remaining numbers in groups of
  `fields`, each passed to the structure constructor `mk` (for example
  `"OpenTheory.Checks.MLP.Layer.mk"`). The kernel reads each field in one projection step. -/
  | records (k fields : Nat) (mk : String)

/-- A registered check. -/
structure Entry where
  /-- Name on the command line. -/
  cli : String
  /-- Fully qualified name of the Lean constant. -/
  const : String
  shape : Shape
  /-- Untrusted: compute the witnesses the check verifies (the identity for most checks). -/
  prepare : List Nat → List Nat := id
  /-- The same check, as a function the compiled lane calls: `const ∘ prepare`. -/
  run : List Nat → Bool

def entries : List Entry :=
  [ { cli := "mlp-exact", const := "OpenTheory.Checks.MLP.check", shape := .records 7 9 "OpenTheory.Checks.MLP.Layer.mk",
      prepare := MLP.prepare, run := fun args => MLP.checkFlat (MLP.prepare args) },
    { cli := "pool", const := "OpenTheory.Checks.poolCheck", shape := .nats 7,
      run := fun | [x, n, l, k, a, b, d] => poolCheck x n l k a b d | _ => false },
    { cli := "pool-witness", const := "OpenTheory.Checks.poolCheckWitness", shape := .nats 9,
      run := fun | [x, n, l, k, a, b, u, v, d] => poolCheckWitness x n l k a b u v d | _ => false } ]

end OpenTheory.Checks
