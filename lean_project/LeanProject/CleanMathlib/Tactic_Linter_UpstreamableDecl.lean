import ImportGraph.Imports
import Mathlib.Tactic.MinImports
open Lean Elab Command
def Lean.Name.isLocal (env : Environment) (decl : Name) : Bool :=
  (env.getModuleIdxFor? decl).isNone
open Mathlib.Command.MinImports
def Lean.Environment.localDefinitionDependencies (env : Environment) (stx id : Syntax) :
    CommandElabM Bool := do
  let declName : NameSet ← try
    NameSet.ofList <$> resolveGlobalConst id
  catch _ =>
    pure ∅
  let immediateDeps ← getAllDependencies stx id
  let immediateDeps : NameSet := immediateDeps.fold (init := ∅) fun s n =>
    if (env.find? n).isSome then s.insert n else s
  let deps ← liftCoreM <| immediateDeps.transitivelyUsedConstants
  let constInfos := deps.toList.filterMap env.find?
  let defs := constInfos.filter (fun constInfo => !(constInfo.isTheorem || constInfo.isCtor))
  return defs.any fun constInfo => !(declName.contains constInfo.name) && constInfo.name.isLocal env
namespace Mathlib.Linter
register_option linter.upstreamableDecl : Bool := {
  defValue := false
  descr := "enable the upstreamableDecl linter"
}
namespace DoubleImports
@[inherit_doc Mathlib.Linter.linter.upstreamableDecl]
def upstreamableDeclLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.upstreamableDecl (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.upstreamableDecl) true)) then return
    let env ← getEnv
    let id ← getId stx
    if id != .missing then
      let minImports := getIrredundantImports env (← getAllImports stx id)
      match minImports with
      | ⟨(RBNode.node _ .leaf upstream _ .leaf), _⟩ => do
        if !(← env.localDefinitionDependencies stx id) then
          let p : GoToModuleLinkProps := { modName := upstream }
          let widget : MessageData := .ofWidget
            (← liftCoreM <| Widget.WidgetInstance.ofHash
              GoToModuleLink.javascriptHash <|
              Server.RpcEncodable.rpcEncode p)
            (toString upstream)
          Linter.logLint linter.upstreamableDecl id
            m!"Consider moving this declaration to the module {widget}."
      | _ => pure ()
initialize addLinter upstreamableDeclLinter
end DoubleImports
end Mathlib.Linter