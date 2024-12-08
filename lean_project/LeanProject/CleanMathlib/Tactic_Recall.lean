import Mathlib.Init
import Lean.Elab.Command
import Lean.Elab.DeclUtil
namespace Mathlib.Tactic.Recall
syntax (name := recall) "recall " ident ppIndent(optDeclSig) (declVal)? : command
open Lean Meta Elab Command Term
elab_rules : command
  | `(recall $id $sig:optDeclSig $[$val?]?) => withoutModifyingEnv do
    let declName := id.getId
    let some info := (← getEnv).find? declName
      | throwError "unknown constant '{declName}'"
    let declConst : Expr := mkConst declName <| info.levelParams.map Level.param
    discard <| liftTermElabM <| addTermInfo id declConst
    let newId := mkIdentFrom id (← mkAuxName declName 1)
    if let some val := val? then
      let some infoVal := info.value?
        | throwErrorAt val "constant '{declName}' has no defined value"
      elabCommand <| ← `(noncomputable def $newId $sig:optDeclSig $val)
      let some newInfo := (← getEnv).find? newId.getId | return 
      liftTermElabM do
        let mvs ← newInfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let newType := newInfo.type.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq info.type newType) do
          throwTypeMismatchError none info.type newInfo.type declConst
        let newVal := newInfo.value?.get!.instantiateLevelParams newInfo.levelParams mvs
        unless (← isDefEq infoVal newVal) do
          let err := m!"\
            value mismatch{indentExpr declConst}\nhas value{indentExpr newVal}\n\
            but is expected to have value{indentExpr infoVal}"
          throwErrorAt val err
    else
      let (binders, type?) := expandOptDeclSig sig
      if let some type := type? then
        runTermElabM fun vars => do
          withAutoBoundImplicit do
            elabBinders binders.getArgs fun xs => do
              let xs ← addAutoBoundImplicits xs
              let type ← elabType type
              Term.synthesizeSyntheticMVarsNoPostponing
              let type ← mkForallFVars xs type
              let type ← mkForallFVars vars type (usedOnly := true)
              unless (← isDefEq info.type type) do
                throwTypeMismatchError none info.type type declConst
      else
        unless binders.getNumArgs == 0 do
          throwError "expected type after ':'"
end Mathlib.Tactic.Recall