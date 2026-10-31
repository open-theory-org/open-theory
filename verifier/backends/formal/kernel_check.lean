import Lean
import Checks.Registry

/-!
# `ot_kernel`: certificate checks evaluated by the Lean kernel

The kernel lane of the fast verifier. For each request it builds the proposition
`@Eq Bool (check args) true`, with the arguments as raw natural literals, and hands the theorem
`Eq.refl true` straight to the kernel: no parser, no elaborator, an environment holding only
Lean's core and the `Checks` modules. Acceptance means the kernel evaluated the check to `true`.
What that implies is proved once in the library, for each registered check.

Usage (same requests as `ot_check`):

    ot_kernel NAME ARGS... [+ NAME ARGS...]    prints true iff every check is accepted
    ot_kernel --stdin                          one request per line, one true/false per line
    ot_kernel --time ...                       also print kernel microseconds to stderr
    ot_kernel --compare ...                    also run the compiled lane (`Entry.run`, what
                                               `ot_check` calls) and report any disagreement

Numbers are decimal or `0x` hexadecimal. Exit code 2 on a usage error, 3 if `--compare` found a
disagreement between the lanes. `--compare` is the differential test of the compiled lane
against the kernel; CI runs it on honest, tampered and randomly corrupted certificates.
-/

open Lean OpenTheory.Checks

/-- Value of an ASCII hex digit. -/
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

def lit (n : Nat) : Expr := .lit (.natVal n)

def listOf (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- The proposition `check args = true`, or why the request is malformed. -/
def requestProp (e : Entry) (args : List Nat) : Except String Expr := do
  let c := mkConst e.const.toName
  let term ← match e.shape with
    | .nats k =>
      if args.length == k then pure (mkAppN c (args.map lit).toArray)
      else throw s!"{e.cli} takes {k} arguments, got {args.length}"
    | .records k g mk =>
      let rest := args.drop k
      if args.length < k || g == 0 || rest.length % g != 0 then
        throw s!"{e.cli} takes {k} arguments, then groups of {g}; got {args.length} in all"
      let mkName := mk.toName
      let records := (List.range (rest.length / g)).map fun i =>
        mkAppN (mkConst mkName) (((rest.drop (i * g)).take g).map lit).toArray
      pure (mkApp (mkAppN c ((args.take k).map lit).toArray) (listOf (mkConst mkName.getPrefix) records))
  return mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) term (mkConst ``Bool.true)

/-- The kernel accepts `Eq.refl true : prop`; otherwise the kernel's reason. -/
def kernelCheck (env : Environment) (prop : Expr) (tag : Nat) : Except Kernel.Exception Unit :=
  let val := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  let decl := Declaration.thmDecl
    { name := .mkSimple s!"ot_kernel_request_{tag}", levelParams := [], type := prop, value := val }
  (env.addDeclCore 0 100000 decl none).map fun _ => ()

/-- A one-line reason for a rejection. The kernel's own message prints the whole term, whose
megabit literals take quadratic time to render in decimal, so only its kind is reported, and
for a mismatch whether the check reduces to `false` or gets stuck. -/
def reason (env : Environment) (prop : Expr) : Kernel.Exception → String
  | .declTypeMismatch .. =>
    match Kernel.whnf env {} prop.appFn!.appArg! with
    | .ok (.const ``Bool.false _) => "the check evaluates to false"
    | .ok e => s!"the check does not reduce to a value (stuck at {e.getAppFn.constName?.getD `_})"
    | .error _ => "the check does not reduce"
  | .deepRecursion => "kernel deep recursion"
  | .deterministicTimeout => "kernel timeout"
  | .excessiveMemory => "kernel out of memory"
  | .interrupted => "interrupted"
  | _ => "kernel error"

/-- Split a request into checks at `+`. -/
def splitChecks (words : List String) : List (List String) :=
  let (cur, done) := words.foldl (fun (cur, done) w =>
    if w == "+" then ([], cur.reverse :: done) else (w :: cur, done)) ([], [])
  ((cur.reverse :: done).reverse).filter (!·.isEmpty)

/-- Run one request. `none` with a message on a usage error. With `compare`, a disagreement
between the kernel and the compiled lane is counted in `disagreements`. -/
def runRequest (env : Environment) (time compare : Bool) (words : List String) (tag : IO.Ref Nat)
    (disagreements : IO.Ref Nat) : IO (Except String Bool) := do
  let checks := splitChecks words
  if checks.isEmpty then return .error "empty request"
  let mut all := true
  for chk in checks do
    let name := chk.head!
    let some e := entries.find? (·.cli == name) | return .error s!"unknown check '{name}'"
    let some args := chk.tail.mapM parseNat | return .error s!"bad number in '{name}'"
    let prop ← match requestProp e (e.prepare args) with
      | .ok p => pure p
      | .error msg => return .error msg
    let n ← tag.modifyGet fun n => (n, n + 1)
    let t0 ← IO.monoNanosNow
    let res := kernelCheck env prop n
    let ok := res matches .ok _
    let t1 ← if ok then IO.monoNanosNow else IO.monoNanosNow
    if time then
      IO.eprintln s!"{name}: {ok}, kernel {(t1 - t0).toFloat / 1000} µs"
      if let .error ex := res then
        IO.eprintln s!"  rejected: {reason env prop ex}"
    if compare then
      let compiled := e.run args
      if compiled != ok then
        disagreements.modify (· + 1)
        IO.eprintln s!"DISAGREE {name}: kernel {ok}, compiled {compiled}"
    all := all && ok
  return .ok all

def usage : String :=
  "usage: ot_kernel [--time] [--compare] NAME ARGS... [+ NAME ARGS...] | ot_kernel [...] --stdin\n" ++
  "checks: " ++ ", ".intercalate (entries.map (·.cli))

def main (argv : List String) : IO UInt32 := do
  let time := argv.contains "--time"
  let compare := argv.contains "--compare"
  let argv := argv.filter (fun a => a != "--time" && a != "--compare")
  -- The `Checks` oleans sit next to the executable: `.lake/build/{bin,lib/lean}`.
  initSearchPath (← findSysroot) [(← IO.appDir) / ".." / "lib" / "lean"]
  let env ← importModules #[{ module := `Checks.Registry }] {}
  let tag ← IO.mkRef 0
  let disagreements ← IO.mkRef 0
  let exitCode := fun (base : UInt32) => do
    return if (← disagreements.get) > 0 then 3 else base
  if argv == ["--stdin"] then
    let stdin ← IO.getStdin
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let words := (line.trimAscii.toString.splitOn " ").filter (· != "")
      if words.isEmpty then continue
      match ← runRequest env time compare words tag disagreements with
      | .ok b => IO.println (toString b)
      | .error msg => IO.println s!"error: {msg}"
      (← IO.getStdout).flush
    exitCode 0
  else
  match ← runRequest env time compare argv tag disagreements with
  | .ok b => IO.println (toString b); exitCode 0
  | .error msg => IO.eprintln s!"{msg}\n{usage}"; return 2
