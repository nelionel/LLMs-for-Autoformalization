import Lean.Elab.Command
import Batteries.Tactic.Unreachable
import Mathlib.Tactic.Linter.Header
open Lean Elab Std
namespace Mathlib.Linter
register_option linter.unusedTactic : Bool := {
  defValue := true
  descr := "enable the unused tactic linter"
}
namespace UnusedTactic
abbrev M := StateRefT (Std.HashMap String.Range Syntax) IO
initialize allowedRef : IO.Ref (Std.HashSet SyntaxNodeKind) ←
  IO.mkRef <| Std.HashSet.empty
    |>.insert `Mathlib.Tactic.Says.says
    |>.insert `Batteries.Tactic.«tacticOn_goal-_=>_»
    |>.insert `by
    |>.insert `null
    |>.insert `«]»
    |>.insert ``Lean.Parser.Term.byTactic
    |>.insert ``Lean.Parser.Tactic.tacticSeq
    |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
    |>.insert ``Lean.Parser.Tactic.tacticTry_
    |>.insert ``Lean.Parser.Tactic.guardHyp
    |>.insert ``Lean.Parser.Tactic.guardTarget
    |>.insert ``Lean.Parser.Tactic.failIfSuccess
    |>.insert `Mathlib.Tactic.successIfFailWithMsg
    |>.insert `Mathlib.Tactic.failIfNoProgress
    |>.insert `Mathlib.Tactic.ExtractGoal.extractGoal
    |>.insert `Mathlib.Tactic.Propose.propose'
    |>.insert `Lean.Parser.Tactic.traceState
    |>.insert `Mathlib.Tactic.tacticMatch_target_
    |>.insert ``Lean.Parser.Tactic.change
    |>.insert `change?
    |>.insert `«tactic#adaptation_note_»
    |>.insert `tacticSleep_heartbeats_
    |>.insert `Mathlib.Tactic.«tacticRename_bvar_→__»
elab "#allow_unused_tactic " ids:ident* : command => do
  let ids := ← Command.liftCoreM do ids.mapM realizeGlobalConstNoOverload
  allowedRef.modify (·.insertMany ids)
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
  IO.mkRef <| Std.HashSet.empty
    |>.insert `Mathlib.Tactic.Says.says
    |>.insert ``Parser.Term.binderTactic
    |>.insert ``Lean.Parser.Term.dynamicQuot
    |>.insert ``Lean.Parser.Tactic.quotSeq
    |>.insert ``Lean.Parser.Tactic.tacticStop_
    |>.insert ``Lean.Parser.Command.notation
    |>.insert ``Lean.Parser.Command.mixfix
    |>.insert ``Lean.Parser.Tactic.discharger
    |>.insert ``Lean.Parser.Tactic.Conv.conv
    |>.insert `Batteries.Tactic.seq_focus
    |>.insert `Mathlib.Tactic.Hint.registerHintStx
    |>.insert `Mathlib.Tactic.LinearCombination.linearCombination
    |>.insert `Mathlib.Tactic.LinearCombination'.linearCombination'
    |>.insert `Aesop.Frontend.Parser.addRules
    |>.insert `Aesop.Frontend.Parser.aesopTactic
    |>.insert `Aesop.Frontend.Parser.aesopTactic?
    |>.insert ``Lean.Parser.Tactic.failIfSuccess
    |>.insert `Mathlib.Tactic.successIfFailWithMsg
    |>.insert `Mathlib.Tactic.failIfNoProgress
def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  k.components.contains `Conv ||
  "slice".isPrefixOf k.toString ||
  match k with
  | .str _ "quot" => true
  | _ => ignoreTacticKinds.contains k
def addIgnoreTacticKind (kind : SyntaxNodeKind) : IO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)
variable (ignoreTacticKinds : NameHashSet) (isTacKind : SyntaxNodeKind → Bool) in
@[specialize] partial def getTactics (stx : Syntax) : M Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM getTactics
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx
def getNames (mctx : MetavarContext) : List Name :=
  let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName
mutual
partial def eraseUsedTacticsList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM eraseUsedTactics
partial def eraseUsedTactics : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      let stx := i.stx
      let kind := stx.getKind
      if let some r := stx.getRange? true then
        if (← allowedRef.get).contains kind
        then modify (·.erase r)
        else
        if i.goalsAfter != i.goalsBefore
        then modify (·.erase r)
        else
        if (kind == `Mathlib.Tactic.«tacticSwap_var__,,») &&
                (getNames i.mctxBefore != getNames i.mctxAfter)
        then modify (·.erase r)
    eraseUsedTacticsList c
  | .context _ t => eraseUsedTactics t
  | .hole _ => pure ()
end
def unusedTacticLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.unusedTactic (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  let trees ← getInfoTrees
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTacticsList trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [`Batteries.Tactic.unreachable, `Batteries.Tactic.unreachableConv] then
      continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"'{stx}' tactic does nothing"
    last := r
initialize addLinter unusedTacticLinter