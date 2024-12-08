import Lean.Elab.Command
import Mathlib.Init
open Lean Elab
namespace Mathlib.Linter
register_option linter.flexible : Bool := {
  defValue := false
  descr := "enable the flexible linter"
}
def flexible? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false
end Mathlib.Linter
section goals_heuristic
namespace Lean.Elab.TacticInfo
def goalsTargetedBy (t : TacticInfo) : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))
def goalsCreatedBy (t : TacticInfo) : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))
end Lean.Elab.TacticInfo
end goals_heuristic
namespace Mathlib.Linter.Flexible
variable (take? : Syntax → Bool) in
partial
def extractCtxAndGoals : InfoTree →
    Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractCtxAndGoals).foldl (· ++ ·) #[]
    if let .ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.goalsTargetedBy, i.goalsCreatedBy)] ++ kargs
      else kargs
    else kargs
  | .context _ t => extractCtxAndGoals t
  | _ => default
inductive Stained
  | name     : Name → Stained
  | goal     : Stained
  | wildcard : Stained
  deriving Repr, Inhabited, DecidableEq, Hashable
instance : ToString Stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"
partial
def toStained : Syntax → Std.HashSet Stained
  | .node _ _ arg => (arg.map toStained).foldl (.union) {}
  | .ident _ _ val _ => {.name val}
  | .atom _ val => match val with
                  | "*" => {.wildcard}
                  | "⊢" => {.goal}
                  | "|" => {.goal}
                  | _ => {}
  | _ => {}
partial
def getStained (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.union) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.union) {}
    | _ => default
def getStained! (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Std.HashSet Stained :=
  let out := getStained stx all?
  if out.size == 0 then {.goal} else out
def Stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : Stained → Array (FVarId × MVarId)
  | name n   => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal     => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)
def stoppers : Std.HashSet Name :=
  { 
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    `Mathlib.Tactic.Abel.abelNF,
    `Mathlib.Tactic.RingNF.ringNF,
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `by,
    ``Lean.Parser.Tactic.tacticTry_,
    `choice,  
    ``Lean.Parser.Tactic.allGoals,
    `Std.Tactic.«tacticOn_goal-_=>_»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    ``cdotTk,
    ``cdot }
def flexible : Std.HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.omega,
    `Mathlib.Tactic.Abel.abel,
    `Mathlib.Tactic.RingNF.ring,
    `Mathlib.Tactic.normNum,
    `linarith,
    `nlinarith,
    ``Lean.Parser.Tactic.tacticNorm_cast_,
    `Aesop.Frontend.Parser.aesopTactic,
    `Mathlib.Tactic.Tauto.tauto,
    `Mathlib.Meta.FunProp.funPropTacStx,
    `Lean.Parser.Tactic.split,
    `Mathlib.Tactic.splitIfs }
def usesGoal? : SyntaxNodeKind → Bool
  | ``Lean.Parser.Tactic.cases => false
  | `Mathlib.Tactic.cases' => false
  | ``Lean.Parser.Tactic.obtain => false
  | ``Lean.Parser.Tactic.tacticHave_ => false
  | ``Lean.Parser.Tactic.rcases => false
  | ``Lean.Parser.Tactic.specialize => false
  | ``Lean.Parser.Tactic.subst => false
  | ``«tacticBy_cases_:_» => false
  | ``Lean.Parser.Tactic.induction => false
  | _ => true
def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)
def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  let name := ldecl.userName
  (getFVarIdCandidates fv name after).getD 0 default
def reallyPersist
    (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
    Array (FVarId × MVarId) := Id.run do
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]
  for (fvar, mvar) in active do       
    match ctx0.decls.find? mvar with  
      | none => 
        new := new.push (fvar, mvar)
      | some mvDecl0 => 
        for mv1 in mvs1 do  
          match ctx1.decls.find? mv1 with  
            | none => dbg_trace "'really_persist' could this happen?" default 
            | some mvDecl1 =>  
              let persisted_fv := persistFVars fvar mvDecl0.lctx mvDecl1.lctx  
              new := new.push (persisted_fv, mv1)
  return inert ++ new
def flexibleLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.flexible (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let x := trees.toList.map (extractCtxAndGoals (fun _ => true))
  let mut stains : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
  let mut msgs : Array (Syntax × Syntax × Stained) := #[]
  for d in x do for (s, ctx0, ctx1, mvs0, mvs1) in d do
    let skind := s.getKind
    if stoppers.contains skind then continue
    let shouldStain? := flexible? s && mvs1.length == mvs0.length
    for d in getStained! s do
      if shouldStain? then
        for currMVar1 in mvs1 do
          let lctx1 := ((ctx1.decls.find? currMVar1).getD default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1
          for l in locsAfter do
            stains := stains.push (l, (d, s))
      else
        let stained_in_syntax := if usesGoal? skind then (toStained s).insert d else toStained s
        if !flexible.contains skind then
          for currMv0 in mvs0 do
            let lctx0 := ((ctx0.decls.find? currMv0).getD default).lctx
            let mut foundFvs : Std.HashSet (FVarId × MVarId):= {}
            for st in stained_in_syntax do
              for d in st.toFMVarId currMv0 lctx0 do
                if !foundFvs.contains d then foundFvs := foundFvs.insert d
            for l in foundFvs do
              if let some (_stdLoc, (st, kind)) := stains.find? (Prod.fst · == l) then
                msgs := msgs.push (s, kind, st)
      let mut new : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
      for (fv, (stLoc, kd)) in stains do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.push (fv, (stLoc, kd))
          dbg_trace "lost {((fv.1.name, fv.2.name), stLoc, kd)}"
        for p in psisted do new := new.push (p, (stLoc, kd))
      stains := new
  for (s, stainStx, d) in msgs do
    Linter.logLint linter.flexible stainStx m!"'{stainStx}' is a flexible tactic modifying '{d}'…"
    logInfoAt s m!"… and '{s}' uses '{d}'!"
initialize addLinter flexibleLinter
end Mathlib.Linter.Flexible