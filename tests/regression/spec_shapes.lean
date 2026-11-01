import Lean
import OpenTheory

/-!
# The specification inside each `Sound` theorem

    lake env lean --run tests/regression/spec_shapes.lean OpenTheory.heldOut_sound …

For each theorem, prints one line `name|model|observable|domain|aggregate`, read from every
`Spec.mk` in its elaborated statement (definitions such as `RateGap.pools` are unfolded to their
constructors). `tests/regression/check_spec_shapes.py` compares the lines with the claim cards, so
a card cannot say `pool` while its theorem says `distribution`.
-/

open Lean Meta

def ctor (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.lastComponentAsString
  | _ => "?"

partial def domain (e : Expr) : MetaM String := do
  let e ← whnf e
  if e.isAppOfArity ``OpenTheory.Domain.pair 3 then
    return s!"pair({← domain e.appFn!.appArg!},{← domain e.appArg!})"
  return ctor e

/-- The model type: a constant's name, or `*` for a variable (the theorem holds for every model). -/
def model (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | _ => "*"

partial def specs (e : Expr) : MetaM (Array String) := do
  match e with
  | .lam n t b bi | .forallE n t b bi =>
    let a ← specs t
    withLocalDecl n bi t fun x => return a ++ (← specs (b.instantiate1 x))
  | .letE n t v b _ =>
    let a ← specs v
    withLetDecl n t v fun x => return a ++ (← specs (b.instantiate1 x))
  | .mdata _ b => specs b
  | .proj _ _ b => specs b
  | .app .. =>
    let args := e.getAppArgs
    let here ← if e.isAppOfArity ``OpenTheory.Spec.mk 5 then
        pure #[s!"{model args[0]!}|{ctor args[2]!}|{← domain args[3]!}|{ctor args[4]!}"]
      else pure #[]
    let mut acc := here ++ (← specs e.getAppFn)
    for a in args do
      acc := acc ++ (← specs a)
    return acc
  | _ => return #[]

def main (names : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `OpenTheory }] {}
  let mut code : UInt32 := 0
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => IO.println s!"{s}|missing"; code := 1
    | some ci =>
      let (out, _) ← (specs ci.type).run' {} |>.toIO { fileName := "", fileMap := default } { env }
      if out.isEmpty then IO.println s!"{s}|none"
      for o in out.toList.eraseDups do IO.println s!"{s}|{o}"
  return code
