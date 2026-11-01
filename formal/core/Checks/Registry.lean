import Checks.MLP
import Checks.PoolRate
import Checks.Tree
import Checks.PoolSample
import Checks.Linear

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
  /-- Structured arguments (trees, boxes, integers) decoded from the naturals by the check's own
  decoder, shared with the compiled lane; `ot_kernel` builds them as constructor terms. -/
  | decoded

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
  /-- What the request decodes to, for the report (`ot_kernel --show`); empty for plain numbers. -/
  render : List Nat → String := fun _ => ""

def entries : List Entry :=
  [ { cli := "mlp-exact", const := "OpenTheory.Checks.MLP.check", shape := .records 7 9 "OpenTheory.Checks.MLP.Layer.mk",
      prepare := MLP.prepare, run := fun args => MLP.checkFlat (MLP.prepare args) },
    { cli := "pool", const := "OpenTheory.Checks.poolCheck", shape := .nats 7,
      run := fun | [x, n, l, k, a, b, d] => poolCheck x n l k a b d | _ => false },
    { cli := "pool-witness", const := "OpenTheory.Checks.poolCheckWitness", shape := .nats 9,
      run := fun | [x, n, l, k, a, b, u, v, d] => poolCheckWitness x n l k a b u v d | _ => false },
    { cli := "pool-sample", const := "OpenTheory.Checks.poolSampleK",
      shape := .records 8 4 "OpenTheory.Checks.Drawn.mk", run := runPoolSample },
    { cli := "pool-sample-witness", const := "OpenTheory.Checks.poolSampleWitnessK",
      shape := .records 10 4 "OpenTheory.Checks.Drawn.mk", run := runPoolSampleWitness },
    { cli := "tree-robust", const := "OpenTheory.Checks.Tree.robustCertK", shape := .decoded,
      run := Tree.runRobust, render := Tree.showRobust },
    { cli := "tree-monotone", const := "OpenTheory.Checks.Tree.monotoneCertK", shape := .decoded,
      run := Tree.runMonotone, render := Tree.showMonotone },
    { cli := "linear-robust", const := "OpenTheory.Checks.Linear.robustK", shape := .decoded,
      run := Linear.runRobust, render := Linear.showRobust },
    { cli := "linear-monotone", const := "OpenTheory.Checks.Linear.monotone", shape := .decoded,
      run := Linear.runMonotone, render := Linear.showMonotone } ]

end OpenTheory.Checks
