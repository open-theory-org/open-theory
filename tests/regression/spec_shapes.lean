import Lean
import OpenTheory

/-!
# The specification of each claim type

    lake env lean --run tests/regression/spec_shapes.lean OpenTheory.ClaimTypes.heldOut …

For each `ClaimType` term (`formal/core/Specs/ClaimTypes.lean`) prints one line

    name|model|observable kind|property|domain|aggregate|Sound theorem

read from its elaborated definition: `model` is the `M` of `ClaimType M X` (`*` for a variable),
`property` the named property its observable applies (the head constant once the binders are
stripped), and the domain is unfolded to its constructors (`RateGap.pools` is a pair of pools).
`tests/regression/check_spec_shapes.py` compares each line with the claim card.
-/

open Lean Meta

def headName (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | _ => "*"

def ctor (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.lastComponentAsString
  | _ => "?"

partial def domain (e : Expr) : MetaM String := do
  let e ← whnf e
  if e.isAppOfArity ``OpenTheory.Domain.pair 3 then
    return s!"pair({← domain e.appFn!.appArg!},{← domain e.appArg!})"
  return ctor e

/-- The named property an observable `.property P` applies. -/
def property (obs : Expr) : MetaM String := do
  let obs ← whnfR obs
  if obs.getAppNumArgs == 0 then return "?"
  lambdaTelescope obs.appArg! fun _ body => return headName body

def shape (ci : ConstantInfo) : MetaM String := do
  let some v := ci.value? | return "not a definition"
  lambdaTelescope v fun _ body => do
    let body ← whnfR body
    unless body.isAppOfArity ``OpenTheory.ClaimType.mk 11 do return "not a ClaimType"
    let args := body.getAppArgs
    let model := args[0]!
    let sound := headName args[10]!
    lambdaTelescope args[7]! fun _ spec => do
      let spec ← whnfR spec
      unless spec.isAppOfArity ``OpenTheory.Spec.mk 5 do return "spec is not a Spec.mk"
      let s := spec.getAppArgs
      return s!"{headName model}|{ctor s[2]!}|{← property s[2]!}|{← domain s[3]!}|{ctor s[4]!}|{sound}"

def main (names : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `OpenTheory }] {}
  let mut code : UInt32 := 0
  for s in names do
    match env.find? s.toName with
    | none => IO.println s!"{s}|missing"; code := 1
    | some ci =>
      let (out, _) ← (shape ci).run' {} |>.toIO { fileName := "", fileMap := default } { env }
      IO.println s!"{s}|{out}"
  return code
