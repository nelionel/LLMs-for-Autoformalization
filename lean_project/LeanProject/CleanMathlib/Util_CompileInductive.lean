import Mathlib.Init
import Lean.Elab.Command
import Lean.Compiler.CSimpAttr
import Lean.Util.FoldConsts
import Lean.Data.AssocList
namespace Mathlib.Util
open Lean Meta
private def replaceConst (repl : AssocList Name Name) (e : Expr) : Expr :=
  e.replace fun | .const n us => repl.find? n |>.map (.const · us) | _ => none
def mkRecNames (all : List Name) (numMotives : Nat) : List Name :=
  if numMotives ≤ all.length then
    all.map mkRecName
  else
    let main := all[0]!
    all.map mkRecName ++
      (List.range (numMotives - all.length)).map (fun i => main.str s!"rec_{i+1}")
private def addAndCompile' (decl : Declaration) : CoreM Unit := do
  try addAndCompile decl
  catch e =>
    match decl with
    | .defnDecl val => throwError "while compiling {val.name}: {e.toMessageData}"
    | .mutualDefnDecl val => throwError "while compiling {val.map (·.name)}: {e.toMessageData}"
    | _ => unreachable!
def compileDefn (dv : DefinitionVal) : MetaM Unit := do
  if ((← getEnv).getModuleIdxFor? dv.name).isNone then
    return ← compileDecl <| .defnDecl dv
  let name ← mkFreshUserName dv.name
  addAndCompile' <| .defnDecl { dv with name }
  let levels := dv.levelParams.map .param
  let old := .const dv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| dv.name.str "eq"
  addDecl <| .thmDecl {
    name
    levelParams := dv.levelParams
    type := ← mkEq old new
    value := ← mkEqRefl old
  }
  Compiler.CSimp.add name .global
open Elab
def isCompiled (env : Environment) (n : Name) : Bool :=
  env.contains (n.str "_cstage2") || (Compiler.CSimp.ext.getState env).map.contains n
elab tk:"compile_def% " i:ident : command => Command.liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  if isCompiled (← getEnv) n then
    logWarningAt tk m!"already compiled {n}"
    return
  let dv ← withRef i <| getConstInfoDefn n
  withRef tk <| compileDefn dv
private def compileStructOnly (iv : InductiveVal) (rv : RecursorVal) : MetaM Unit := do
  let value ← forallTelescope rv.type fun xs _ =>
    let val := xs[rv.getFirstMinorIdx]!
    let val := mkAppN val ⟨.map (xs[rv.getMajorIdx]!.proj iv.name) <| .range rv.rules[0]!.nfields⟩
    mkLambdaFVars xs val
  go value
where
  go value := do
    let name ← mkFreshUserName rv.name
    addAndCompile' <| .defnDecl { rv with
      name
      value
      hints := .abbrev
      safety := .safe
    }
    let levels := rv.levelParams.map .param
    let old := .const rv.name levels
    let new := .const name levels
    let name ← mkFreshUserName <| rv.name.str "eq"
    addDecl <| .mutualDefnDecl [{
      name
      levelParams := rv.levelParams
      type := ← mkEq old new
      value := .const name levels
      hints := .opaque
      safety := .partial
    }]
    Compiler.CSimp.add name .global
    compileDefn <| ← getConstInfoDefn <| mkRecOnName iv.name
def compileInductiveOnly (iv : InductiveVal) (warn := true) : MetaM Unit := do
  let rv ← getConstInfoRec <| mkRecName iv.name
  if ← isProp rv.type then
    if warn then logWarning m!"not compiling {rv.name}"
    return
  if isCompiled (← getEnv) rv.name then
    if warn then logWarning m!"already compiled {rv.name}"
    return
  if !iv.isRec && rv.numMotives == 1 && iv.numCtors == 1 && iv.numIndices == 0 then
    compileStructOnly iv rv
    return
  let levels := rv.levelParams.map .param
  let rvs ←
    if rv.numMotives == 1 then pure [rv]
    else mkRecNames iv.all rv.numMotives |>.mapM getConstInfoRec
  let rvs ← rvs.mapM fun rv => return (rv, ← mkFreshUserName rv.name)
  let repl := rvs.foldl (fun l (rv, name) => .cons rv.name name l) .nil
  addAndCompile' <| .mutualDefnDecl <|← rvs.mapM fun (rv, name) => do
    pure { rv with
      name
      value := ← forallTelescope rv.type fun xs body => do
        let major := xs[rv.getMajorIdx]!
        (← whnfD <| ← inferType major).withApp fun head args => do
          let .const iv levels' := head | throwError "not an inductive"
          let iv ← getConstInfoInduct iv
          let rv' ← getConstInfoRec <| mkRecName iv.name
          if !iv.isRec && rv'.numMotives == 1 && iv.numCtors == 1 && iv.numIndices == 0 then
            let rule := rv.rules[0]!
            let val := .beta (replaceConst repl rule.rhs) xs[:rv.getFirstIndexIdx]
            let val := .beta val ⟨.map (major.proj iv.name) <| .range rule.nfields⟩
            mkLambdaFVars xs val
          else
            let val := .const (mkCasesOnName iv.name) (.param rv.levelParams.head! :: levels')
            let val := mkAppN val args[:rv'.numParams]
            let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
            let val := mkAppN val xs[rv.getFirstIndexIdx:]
            let val := mkAppN val <| rv.rules.toArray.map fun rule =>
              .beta (replaceConst repl rule.rhs) xs[:rv.getFirstIndexIdx]
            mkLambdaFVars xs val
      hints := .opaque
      safety := .partial
    }
  for (rv, name) in rvs do
    let old := .const rv.name levels
    let new := .const name levels
    let name ← mkFreshUserName <| rv.name.str "eq"
    addDecl <| .mutualDefnDecl [{
      name
      levelParams := rv.levelParams
      type := ← mkEq old new
      value := .const name levels
      hints := .opaque
      safety := .partial
    }]
    Compiler.CSimp.add name .global
  for name in iv.all do
    for aux in [mkRecOnName name, mkBRecOnName name] do
      if let some (.defnInfo dv) := (← getEnv).find? aux then
        compileDefn dv
mutual
partial def compileInductive (iv : InductiveVal) (warn := true) : MetaM Unit := do
  compileInductiveOnly iv warn
  compileSizeOf iv
partial def compileSizeOf (iv : InductiveVal) : MetaM Unit := do
  let go aux := do
    if let some (.defnInfo dv) := (← getEnv).find? aux then
      if !isCompiled (← getEnv) aux then
        let deps : NameSet := dv.value.foldConsts ∅ fun c arr =>
          if let .str name "_sizeOf_inst" := c then arr.insert name else arr
        for i in deps do
          if let some (.inductInfo iv) := (← getEnv).find? i then
            compileInductive iv (warn := false)
        compileDefn dv
  let rv ← getConstInfoRec <| mkRecName iv.name
  for name in iv.all do
    for i in [:rv.numMotives] do
      go <| name.str s!"_sizeOf_{i+1}"
    go <| name.str "_sizeOf_inst"
end
elab tk:"compile_inductive% " i:ident : command => Command.liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo i
  let iv ← withRef i <| getConstInfoInduct n
  withRef tk <| compileInductive iv
end Mathlib.Util
compile_def% Nat.recOn
compile_def% Nat.brecOn
compile_inductive% Prod
compile_inductive% List
compile_inductive% PUnit
compile_inductive% PEmpty
compile_inductive% Sum
compile_inductive% PSum
compile_inductive% And
compile_inductive% False
compile_inductive% Empty
compile_inductive% Bool
compile_inductive% Sigma
private unsafe def Float.valUnsafe : Float → floatSpec.float := unsafeCast
private unsafe def Float.mkUnsafe : floatSpec.float → Float := unsafeCast
@[implemented_by Float.valUnsafe] private def Float.valImpl (x : Float) : floatSpec.float := x.1
@[implemented_by Float.mkUnsafe] private def Float.mkImpl (x : floatSpec.float) : Float := ⟨x⟩
@[csimp] private theorem Float.val_eq : @Float.val = Float.valImpl := rfl
@[csimp] private theorem Float.mk_eq : @Float.mk = Float.mkImpl := rfl
open Lean Meta Elab Mathlib.Util in
run_cmd Command.liftTermElabM do
  for n in [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float] do
    let iv ← getConstInfoInduct n
    let rv ← getConstInfoRec <| mkRecName n
    let value ← Elab.Term.elabTerm (← `(fun H t => H t.1))
      (← inferType (.const rv.name (rv.levelParams.map .param)))
    compileStructOnly.go iv rv value
    compileSizeOf iv
compile_inductive% String
compile_inductive% Lean.Name
compile_def% Lean.Name.sizeOf
compile_def% Lean.instSizeOfName