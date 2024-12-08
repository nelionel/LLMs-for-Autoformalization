import Mathlib.Init
import Lean.Elab.Command
import Lean.Server.InfoUtils
open Lean Elab Command Meta
namespace Mathlib.Linter
register_option linter.haveLet : Nat := {
  defValue := 0
  descr := "enable the `have` vs `let` linter:\n\
            * 0 
            * 1 
            * 2 or more 
}
namespace haveLet
partial
def isHave? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave_ _ => true
  |_ => false
end haveLet
end Mathlib.Linter
namespace Mathlib.Linter.haveLet
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) :
    InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)
def areProp_toFormat (ctx : ContextInfo) (lc : LocalContext) (es : Array Expr) :
    CommandElabM (Array (Bool × Format)) := do
  ctx.runMetaM lc do
    es.mapM fun e => do
      let typ ← inferType (← instantiateMVars e)
      return (typ.isProp, ← ppExpr e)
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format)) :=
  InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := (i.goalsAfter.map (mctx.decls.find? ·)).reduceOption
    let largestIdx := mvdecls.toArray.qsort (·.index > ·.index)
    let lc := (largestIdx.getD 0 default).lctx
    let oldMvdecls := (i.goalsBefore.map (mctx.decls.find? ·)).reduceOption
    let oldLctx := oldMvdecls.map (·.lctx)
    let oldDecls := (oldLctx.map (·.decls.toList.reduceOption)).flatten
    let oldFVars := oldDecls.map (·.fvarId)
    let newDecls := lc.decls.toList.reduceOption.filter (! oldFVars.contains ·.fvarId)
    let fmts ← areProp_toFormat ctx lc (newDecls.map (·.type)).toArray
    let (_propFmts, typeFmts) := (fmts.zip (newDecls.map (·.userName)).toArray).partition (·.1.1)
    return typeFmts.map fun ((_, fmt), na) => (stx, f!"{na} : {fmt}"))
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, fmt) in ← nonPropHaves t do
        logWarningAt s <| .tagged linter.haveLet.name
          m!"'{fmt}' is a Type and not a Prop. Consider using 'let' instead of 'have'.\n\
          You can disable this linter using `set_option linter.haveLet 0`"
initialize addLinter haveLetLinter
end haveLet
end Mathlib.Linter