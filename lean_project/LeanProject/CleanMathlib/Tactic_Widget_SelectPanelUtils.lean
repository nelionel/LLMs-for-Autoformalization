import Lean.Meta.ExprLens
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.OfRpcMethod 
import Mathlib.Tactic.Widget.SelectInsertParamsClass
open Lean Meta Server
open Lean.SubExpr in
def getGoalLocations (locations : Array GoalsLocation) : Array SubExpr.Pos := Id.run do
  let mut res := #[]
  for location in locations do
    if let .target pos := location.loc then
      res := res.push pos
  return res
def insertMetaVar (e : Expr) (pos : SubExpr.Pos) : MetaM Expr :=
  replaceSubexpr (fun _ ↦ do mkFreshExprMVar none .synthetic) pos e
def String.renameMetaVar (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++ "?_".intercalate (tail.map fun s ↦ s.dropWhile Char.isDigit)
open ProofWidgets
structure SelectInsertParams where
  pos : Lsp.Position
  goals : Array Widget.InteractiveGoal
  selectedLocations : Array SubExpr.GoalsLocation
  replaceRange : Lsp.Range
  deriving SelectInsertParamsClass, RpcEncodable
open scoped Jsx in open SelectInsertParamsClass Lean.SubExpr in
def mkSelectionPanelRPC {Params : Type} [SelectInsertParamsClass Params]
    (mkCmdStr : (pos : Array GoalsLocation) → (goalType : Expr) → Params →
   MetaM (String × String × Option (String.Pos × String.Pos)))
  (helpMsg : String) (title : String) (onlyGoal := true) (onlyOne := false) :
  (params : Params) → RequestM (RequestTask Html) :=
fun params ↦ RequestM.asTask do
let doc ← RequestM.readDoc
if h : 0 < (goals params).size then
  let mainGoal := (goals params)[0]
  let mainGoalName := mainGoal.mvarId.name
  let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
  let be_where := if onlyGoal then "in the main goal." else "in the main goal or its context."
  let errorMsg := s!"{all} should be {be_where}"
  let inner : Html ← (do
    if onlyOne && (selectedLocations params).size > 1 then
      return <span>{.text "You should select only one sub-expression"}</span>
    for selectedLocation in selectedLocations params do
      if selectedLocation.mvarId.name != mainGoalName then
        return <span>{.text errorMsg}</span>
      else if onlyGoal then
        if !(selectedLocation.loc matches (.target _)) then
          return <span>{.text errorMsg}</span>
    if (selectedLocations params).isEmpty then
      return <span>{.text helpMsg}</span>
    mainGoal.ctx.val.runMetaM {} do
      let md ← mainGoal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        let (linkText, newCode, range?) ← mkCmdStr (selectedLocations params) md.type.consumeMData
          params
        return .ofComponent
          MakeEditLink
          (.ofReplaceRange doc.meta (replaceRange params) newCode range?)
          #[ .text linkText ])
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1">{inner}</div>
    </details>
else
  return <span>{.text "There is no goal to solve!"}</span> 