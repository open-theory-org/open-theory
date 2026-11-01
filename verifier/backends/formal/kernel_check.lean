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
    ot_kernel --show ...                       also print what each request decodes to (stderr)
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

/-! ### Constructor terms for the tree checks (`Shape.decoded`) -/

section
open OpenTheory.Checks.Tree
open OpenTheory.Checks (Linear.decRobust Linear.decMonotone)

def intE : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (lit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (lit n)

def boolE (b : Bool) : Expr := mkConst (if b then ``Bool.true else ``Bool.false)

def boundE (b : Bound) : Expr :=
  let opt : Option Int → Expr
    | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Int)
    | some z => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Int) (intE z)
  mkApp2 (mkConst ``Bound.mk) (opt b.lo) (opt b.hi)

def treeE : Tree → Expr
  | .leaf v => mkApp (mkConst ``Tree.leaf) (intE v)
  | .node f t l r => mkApp4 (mkConst ``Tree.node) (lit f) (intE t) (treeE l) (treeE r)

def cutsE : Cuts → Expr
  | .none => mkConst ``Cuts.none
  | .cut c l r => mkApp3 (mkConst ``Cuts.cut) (intE c) (cutsE l) (cutsE r)

def boxE (B : Box) : Expr := listOf (mkConst ``Bound) (B.map boundE)

/-- The arguments of a decoded check, as constructor terms, in the order of its constant. -/
def decodedArgs (cli : String) (args : List Nat) : Except String (Array Expr) :=
  match cli with
  | "tree-robust" => match decRobust args with
    | some (base, τ, c, B, ts, ms) => pure #[intE base, intE τ, listOf (mkConst ``Tree) (ts.map treeE),
        listOf (mkConst ``Int) (ms.map intE), boxE B, boolE c]
    | none => throw "tree-robust: malformed request"
  | "tree-monotone" => match decMonotone args with
    | some (j, up, B, ts, cs) => pure #[lit j, boolE up, listOf (mkConst ``Tree) (ts.map treeE), boxE B,
        listOf (mkConst ``Cuts) (cs.map cutsE)]
    | none => throw "tree-monotone: malformed request"
  | "linear-robust" => match Linear.decRobust args with
    | some (bias, τ, c, B, ws) => pure #[intE bias, intE τ, listOf (mkConst ``Int) (ws.map intE), boxE B, boolE c]
    | none => throw "linear-robust: malformed request"
  | "linear-monotone" => match Linear.decMonotone args with
    | some (j, up, ws) => pure #[listOf (mkConst ``Int) (ws.map intE), lit j, boolE up]
    | none => throw "linear-monotone: malformed request"
  | _ => throw s!"{cli}: no decoder"
end

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
    | .decoded => pure (mkAppN c (← decodedArgs e.cli args))
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
def runRequest (env : Environment) (time compare showIt : Bool) (words : List String) (tag : IO.Ref Nat)
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
    if showIt && e.render args != "" then
      IO.eprintln s!"decoded {name}: {e.render args}"
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
  let showIt := argv.contains "--show"
  let argv := argv.filter (fun a => a != "--time" && a != "--compare" && a != "--show")
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
      match ← runRequest env time compare showIt words tag disagreements with
      | .ok b => IO.println (toString b)
      | .error msg => IO.println s!"error: {msg}"
      (← IO.getStdout).flush
    exitCode 0
  else
  match ← runRequest env time compare showIt argv tag disagreements with
  | .ok b => IO.println (toString b); exitCode 0
  | .error msg => IO.eprintln s!"{msg}\n{usage}"; return 2
