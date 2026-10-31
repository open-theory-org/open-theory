import Foundations.Arithmetic.FastCheck

/-! # `ot_check`: run certificate decision procedures as compiled code

  ot_check pool <x> <n> <k> <a> <b> <d>
  ot_check pool-witness <x> <n> <k> <a> <b> <u> <v> <d>
  ot_check CHECK + CHECK + ...                 (true when all are)

Numbers are decimal or `0x` hexadecimal. Prints `true` or `false` and exits 0, or exits 2 on a
usage error. The functions run are the `FastCheck` definitions themselves, compiled; what `true`
means is proved once in `Specs.PoolRate` (`Claim.of_poolCheck`, `Claim.of_poolCheckWitness`). -/

open OpenTheory.FastCheck

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a decimal or `0x` hexadecimal natural number. -/
def parseNat (s : String) : Option Nat :=
  let (base, digits) := if s.startsWith "0x" then (16, (s.drop 2).toString.toList) else (10, s.toList)
  if digits.isEmpty then none else
  digits.foldlM (fun acc c => do
    let d ← hexDigit c
    if d < base then some (acc * base + d) else none) 0

def check : List String → Option Bool
  | ["pool", x, n, k, a, b, d] => do
    return poolCheck (← parseNat x) (← parseNat n) (← parseNat k) (← parseNat a) (← parseNat b)
      (← parseNat d)
  | ["pool-witness", x, n, k, a, b, u, v, d] => do
    return poolCheckWitness (← parseNat x) (← parseNat n) (← parseNat k) (← parseNat a)
      (← parseNat b) (← parseNat u) (← parseNat v) (← parseNat d)
  | _ => none

/-- Split arguments at `+`. -/
def splitPlus : List String → List (List String)
  | [] => [[]]
  | "+" :: rest => [] :: splitPlus rest
  | a :: rest =>
    match splitPlus rest with
    | [] => [[a]]
    | g :: gs => (a :: g) :: gs

/-- Several checks separated by `+`: true when all are. -/
def checkAll (args : List String) : Option Bool :=
  (splitPlus args).foldlM (fun acc group => do return acc && (← check group)) true

def main (args : List String) : IO UInt32 := do
  match checkAll args with
  | some r => IO.println (if r then "true" else "false"); return 0
  | none =>
    IO.eprintln "usage: ot_check CHECK [+ CHECK ...], CHECK = pool x n k a b d | pool-witness x n k a b u v d"
    return 2
