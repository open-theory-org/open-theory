import Checks.Registry

/-! # `ot_check`: certificate checks run as compiled code

The compiled lane of the fast verifier. Same requests as `ot_kernel`:

    ot_check NAME ARGS... [+ NAME ARGS...]    prints true iff every check is accepted
    ot_check --stdin                          one request per line, one true/false per line

Numbers are decimal or `0x` hexadecimal; exit code 2 on a usage error. Each check is the
registry entry's `run`, the compiled form of the constant `ot_kernel` hands to the kernel. A
compiled run trusts the Lean compiler, so its result is never labelled `verified`
(specs/protocols/assurance-levels.md); `ot_kernel --compare` checks that both lanes agree.
-/

open OpenTheory.Checks

def hexVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b - 48).toNat
  else if 97 ≤ b && b ≤ 102 then some (b - 87).toNat
  else if 65 ≤ b && b ≤ 70 then some (b - 55).toNat
  else none

/-- Hex digits `bs[i:j]`, by halving so that a megabit number parses in linear-log time. -/
partial def parseHex (bs : ByteArray) (i j : Nat) : Option Nat :=
  if j - i ≤ 15 then
    (List.range (j - i)).foldlM (fun acc k => (hexVal bs[i + k]!).map (acc * 16 + ·)) 0
  else
    let m := (i + j) / 2
    return ((← parseHex bs i m) <<< (4 * (j - m))) ||| (← parseHex bs m j)

def parseNat (s : String) : Option Nat :=
  if s.startsWith "0x" then
    let bs := (s.drop 2).toString.toUTF8
    if bs.size == 0 then none else parseHex bs 0 bs.size
  else s.toNat?

/-- Split a request into checks at `+`. -/
def splitChecks (words : List String) : List (List String) :=
  let (cur, done) := words.foldl (fun (cur, done) w =>
    if w == "+" then ([], cur.reverse :: done) else (w :: cur, done)) ([], [])
  ((cur.reverse :: done).reverse).filter (!·.isEmpty)

/-- One check, or why the request is malformed. -/
def runCheck (words : List String) : Except String Bool := do
  let name := words.head!
  let some e := entries.find? (·.cli == name) | throw s!"unknown check '{name}'"
  let some args := words.tail.mapM parseNat | throw s!"bad number in '{name}'"
  if let .nats k := e.shape then
    if args.length != k then throw s!"{name} takes {k} arguments, got {args.length}"
  return e.run args

def usage : String :=
  "usage: ot_check NAME ARGS... [+ NAME ARGS...]\nchecks: " ++ ", ".intercalate (entries.map (·.cli))

def main (argv : List String) : IO UInt32 := do
  if argv == ["--stdin"] then
    let stdin ← IO.getStdin
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let words := (line.trimAscii.toString.splitOn " ").filter (· != "")
      if words.isEmpty then continue
      match (splitChecks words).mapM runCheck with
      | .ok rs => IO.println (toString (rs.all id))
      | .error msg => IO.println s!"error: {msg}"
      (← IO.getStdout).flush
    return 0
  let checks := splitChecks argv
  if checks.isEmpty then IO.eprintln usage; return 2
  match checks.mapM runCheck with
  | .ok rs => IO.println (toString (rs.all id)); return 0
  | .error msg => IO.eprintln s!"{msg}\n{usage}"; return 2
