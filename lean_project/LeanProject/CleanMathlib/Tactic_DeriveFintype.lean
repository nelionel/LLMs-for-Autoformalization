import Mathlib.Tactic.ProxyType
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
namespace Mathlib.Deriving.Fintype
open Lean Elab Lean.Parser.Term
open Meta Command
macro "derive_fintype% " t:term : term => `(term| Fintype.ofEquiv _ (proxy_equiv% $t))
def mkFintype (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmd ← liftTermElabM do
    let header ← Deriving.mkHeader `Fintype 0 indVal
    let binders' ← Deriving.mkInstImplicitBinders `Decidable indVal header.argNames
    let instCmd ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          Fintype $header.targetType := derive_fintype% _)
    return instCmd
  trace[Elab.Deriving.fintype] "instance command:\n{cmd}"
  elabCommand cmd
  return true
def mkFintypeEnum (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let levels := indVal.levelParams.map Level.param
  let toCtorIdxName := declName.mkStr "toCtorIdx"
  let enumListName := declName.mkStr "enumList"
  let toCtorThmName := declName.mkStr "enumList_get?_to_CtorIdx_eq"
  let enumListNodupName := declName.mkStr "enumList_nodup"
  liftTermElabM <| Term.withoutErrToSorry do
    do 
      trace[Elab.Deriving.fintype] "defining {enumListName}"
      let type := mkConst declName levels
      let listType ← mkAppM ``List #[type]
      let listNil ← mkAppOptM ``List.nil #[some type]
      let listCons name xs := mkAppM ``List.cons #[mkConst name levels, xs]
      let enumList ← indVal.ctors.foldrM (listCons · ·) listNil
      addAndCompile <| Declaration.defnDecl
        { name := enumListName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := listType
          value := enumList }
      setProtected enumListName
      addDocString enumListName s!"A list enumerating every element of the type, \
        which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)"
    do 
      trace[Elab.Deriving.fintype] "proving {toCtorThmName}"
      let goalStx ← `(term| ∀ (x : $(← Term.exprToSyntax <| mkConst declName levels)),
        List.get? $(mkIdent enumListName) ($(mkIdent toCtorIdxName) x) = some x)
      let goal ← Term.elabTerm goalStx (mkSort .zero)
      let pf ← Term.elabTerm (← `(term| by intro x; cases x <;> rfl)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      addAndCompile <| Declaration.thmDecl
        { name := toCtorThmName
          levelParams := indVal.levelParams
          type := ← instantiateMVars goal
          value := ← instantiateMVars pf }
      setProtected toCtorThmName
    do 
      trace[Elab.Deriving.fintype] "proving {enumListNodupName}"
      let enum ← Term.exprToSyntax <| mkConst enumListName levels
      let goal ← Term.elabTerm (← `(term| List.Nodup $enum)) (mkSort .zero)
      let n : TSyntax `term := quote indVal.numCtors
      let pf ← Term.elabTerm (← `(term| by
                  apply List.Nodup.of_map $(mkIdent toCtorIdxName)
                  have h : List.map $(mkIdent toCtorIdxName) $(mkIdent enumListName)
                            = List.range $n := rfl
                  exact h ▸ List.nodup_range $n)) goal
      Term.synthesizeSyntheticMVarsNoPostponing
      addAndCompile <| Declaration.thmDecl
        { name := enumListNodupName
          levelParams := indVal.levelParams
          type := ← instantiateMVars goal
          value := ← instantiateMVars pf }
      setProtected enumListNodupName
  trace[Elab.Deriving.fintype] "defining fintype instance"
  let cmd ← `(command|
    instance : Fintype $(mkIdent declName) where
      elems := Finset.mk $(mkIdent enumListName) $(mkIdent enumListNodupName)
      complete := by
        intro x
        rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_get?]
        exact ⟨$(mkIdent toCtorIdxName) x, $(mkIdent toCtorThmName) x⟩)
  trace[Elab.Deriving.fintype] "instance command:\n{cmd}"
  elabCommand cmd
def mkFintypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false 
  let declName := declNames[0]!
  if ← isEnumType declName then
    mkFintypeEnum declName
    return true
  else
    mkFintype declName
initialize
  registerDerivingHandler ``Fintype mkFintypeInstanceHandler
  registerTraceClass `Elab.Deriving.fintype
end Mathlib.Deriving.Fintype