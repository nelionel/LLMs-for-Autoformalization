import Mathlib.Init
import ImportGraph.Imports
open Lean Elab Command
namespace Mathlib.Command.MinImports
partial
def getSyntaxNodeKinds : Syntax → NameSet
  | .node _ kind args =>
    ((args.map getSyntaxNodeKinds).foldl (NameSet.append · ·) {}).insert kind
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}
def getVisited (env : Environment) (decl : Name) : NameSet :=
  let (_, { visited, .. }) := CollectAxioms.collect decl |>.run env |>.run {}
  visited
def getId (stx : Syntax) : CommandElabM Syntax := do
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      match stx.find? (·.isOfKind ``Lean.Parser.Command.instance) with
        | none => return .missing
        | some stx => do
          let dv ← mkDefViewOfInstance {} stx
          return dv.declId[0]
partial
def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}
def getAttrNames (stx : Syntax) : NameSet :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx
def getAttrs (env : Environment) (stx : Syntax) : NameSet :=
  Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new
def previousInstName : Name → Name
  | nm@(.str init tail) =>
    let last := tail.takeRightWhile (· != '_')
    let newTail := match last.toNat? with
                    | some (n + 2) => s!"_{n + 1}"
                    | _ => ""
    let newTailPrefix := tail.dropRightWhile (· != '_')
    if newTailPrefix.isEmpty then nm else
    let newTail :=
      (if newTailPrefix.back == '_' then newTailPrefix.dropRight 1 else newTailPrefix) ++ newTail
    .str init newTail
  | nm => nm
def getAllDependencies (cmd id : Syntax) :
    CommandElabM NameSet := do
  let env ← getEnv
  let id1 ← getId cmd
  let ns ← getCurrNamespace
  let id2 := mkIdentFrom id1 (previousInstName id1.getId)
  let nm ← liftCoreM do (
    realizeGlobalConstNoOverload id1 <|>
    realizeGlobalConstNoOverload id2 <|>
    return ns ++ id1.getId)
  return getVisited env nm
              |>.append (getVisited env id.getId)
              |>.append (getSyntaxNodeKinds cmd)
              |>.append (getAttrs env cmd)
def getAllImports (cmd id : Syntax) (dbg? : Bool := false) :
    CommandElabM NameSet := do
  let env ← getEnv
  let ts ← getAllDependencies cmd id
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : Std.HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.insert ((env.getModuleIdx? imp).getD default) imp
  let mut fins : NameSet := {}
  for t in ts do
    let new := match env.getModuleIdxFor? t with
      | some t => (hm.get? t).get!
      | none   => .anonymous 
    if !fins.contains new then fins := fins.insert new
  return fins.erase .anonymous
def getIrredundantImports (env : Environment) (importNames : NameSet) : NameSet :=
  importNames.diff (env.findRedundantImports importNames.toArray)
def minImpsCore (stx id : Syntax) : CommandElabM Unit := do
    let tot := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let fileNames := tot.toArray.qsort Name.lt
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"
syntax (name := minImpsStx) "#min_imports" "in" command : command
@[inherit_doc minImpsStx]
syntax "#min_imports" "in" term : command
elab_rules : command
  | `(#min_imports in $cmd:command) => do
    let id ← getId cmd
    Elab.Command.elabCommand cmd <|> pure ()
    minImpsCore cmd id
  | `(#min_imports in $cmd:term) => minImpsCore cmd cmd
end Mathlib.Command.MinImports