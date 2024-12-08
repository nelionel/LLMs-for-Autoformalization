import Mathlib.Init
import Lean.Meta.Tactic.Util
import Lean.Elab.Tactic.Basic
namespace Mathlib.Tactic
open Lean Meta Elab Tactic
initialize registerTraceClass `tactic.use
def applyTheConstructor (mvarId : MVarId) :
    MetaM (List MVarId × List MVarId × List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `constructor
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId
                  m!"target is not an inductive datatype{indentExpr target}")
      fun ival us => do
        match ival.ctors with
        | [ctor] =>
          let cinfo ← getConstInfoCtor ctor
          let ctorConst := Lean.mkConst ctor us
          let (args, binderInfos, _) ← forallMetaTelescopeReducing (← inferType ctorConst)
          let mut explicit := #[]
          let mut implicit := #[]
          let mut insts := #[]
          for arg in args, binderInfo in binderInfos, i in [0:args.size] do
            if cinfo.numParams ≤ i ∧ binderInfo.isExplicit then
              explicit := explicit.push arg.mvarId!
            else
              implicit := implicit.push arg.mvarId!
              if binderInfo.isInstImplicit then
                insts := insts.push arg.mvarId!
          let e := mkAppN ctorConst args
          let eType ← inferType e
          unless (← withAssignableSyntheticOpaque <| isDefEq eType target) do
            throwError m!"type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg eType target}"
          mvarId.assign e
          return (explicit.toList, implicit.toList, insts.toList)
        | _ => throwTacticEx `constructor mvarId
                m!"target inductive type does not have exactly one constructor{indentExpr target}"
partial
def useLoop (eager : Bool) (gs : List MVarId) (args : List Term) (acc insts : List MVarId) :
    TermElabM (List MVarId × List MVarId × List MVarId) := do
  trace[tactic.use] "gs = {gs}\nargs = {args}\nacc = {acc}"
  match gs, args with
  | gs, [] =>
    return (gs, acc, insts)
  | [], arg :: _ =>
    throwErrorAt arg "too many arguments supplied to `use`"
  | g :: gs', arg :: args' => g.withContext do
    if ← g.isAssigned then
      let e ← Term.elabTermEnsuringType arg (← g.getType)
      unless ← isDefEq e (.mvar g) do
        throwErrorAt arg
          "argument is not definitionally equal to inferred value{indentExpr (.mvar g)}"
      return ← useLoop eager gs' args' acc insts
    let refineArg ← `(tactic| refine ($arg : $(← Term.exprToSyntax (← g.getType))))
    if eager then
      if let some newGoals ← observing? (run g do withoutRecover <| evalTactic refineArg) then
        return ← useLoop eager gs' args' (acc ++ newGoals) insts
    if eager || gs'.isEmpty then
      if let some (expl, impl, insts') ← observing? do
                try applyTheConstructor g
                catch e => trace[tactic.use] "Constructor. {e.toMessageData}"; throw e then
        trace[tactic.use] "expl.length = {expl.length}, impl.length = {impl.length}"
        return ← useLoop eager (expl ++ gs') args (acc ++ impl) (insts ++ insts')
    let newGoals ← run g do evalTactic refineArg
    useLoop eager gs' args' (acc ++ newGoals) insts
def runUse (eager : Bool) (discharger : TacticM Unit) (args : List Term) : TacticM Unit := do
  let egoals ← focus do
    let (egoals, acc, insts) ← useLoop eager (← getGoals) args [] []
    for inst in insts do
      if !(← inst.isAssigned) then
        discard <| inst.withContext <| observing? do inst.assign (← synthInstance (← inst.getType))
    setGoals (egoals ++ acc)
    pruneSolvedGoals
    pure egoals
  for g in egoals do
    if !(← g.isAssigned) then
      g.withContext do
        if ← isProp (← g.getType) then
          trace[tactic.use] "running discharger on {g}"
          discard <| run g discharger
syntax "use_discharger" : tactic
macro_rules | `(tactic| use_discharger) => `(tactic| apply exists_prop.mpr <;> use_discharger)
macro_rules | `(tactic| use_discharger) => `(tactic| apply And.intro <;> use_discharger)
macro_rules | `(tactic| use_discharger) => `(tactic| rfl)
macro_rules | `(tactic| use_discharger) => `(tactic| assumption)
macro_rules | `(tactic| use_discharger) => `(tactic| apply True.intro)
def mkUseDischarger (discharger? : Option (TSyntax ``Parser.Tactic.discharger)) :
    TacticM (TacticM Unit) := do
  let discharger ←
    if let some disch := discharger? then
      match disch with
      | `(Parser.Tactic.discharger| ($_ := $d)) => `(tactic| ($d))
      | _ => throwUnsupportedSyntax
    else
      `(tactic| try with_reducible use_discharger)
  return evalTactic discharger
elab (name := useSyntax)
    "use" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse false (← mkUseDischarger discharger?) args.getElems.toList
@[inherit_doc useSyntax]
elab "use!" discharger?:(Parser.Tactic.discharger)? ppSpace args:term,+ : tactic => do
  runUse true (← mkUseDischarger discharger?) args.getElems.toList
end Mathlib.Tactic