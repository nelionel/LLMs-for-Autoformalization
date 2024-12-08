import Mathlib.Init
import Lean.Elab.Tactic.Simp
open Lean Elab.Tactic
def Lean.PHashSet.toList.{u} {α : Type u} [BEq α] [Hashable α] (s : Lean.PHashSet α) : List α :=
  s.1.toList.map (·.1)
namespace Lean
namespace Meta.Simp
open Elab.Tactic
instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.values.toList}
post:
{s.post.values.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"
def Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result
end Simp
def simpTheoremsOfNames (lemmas : List Name := []) (simpOnly : Bool := false) :
    MetaM SimpTheorems := do
  lemmas.foldlM (·.addConst ·)
    (← if simpOnly then
      simpOnlyBuiltins.foldlM (·.addConst ·) {}
    else
      getSimpTheorems)
def Simp.Context.ofNames (lemmas : List Name := []) (simpOnly : Bool := false)
    (config : Simp.Config := {}) : MetaM Simp.Context := do
  Simp.mkContext config
    (simpTheorems := #[← simpTheoremsOfNames lemmas simpOnly])
    (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)
def simpOnlyNames (lemmas : List Name) (e : Expr) (config : Simp.Config := {}) :
    MetaM Simp.Result := do
  (·.1) <$> simp e (← Simp.Context.ofNames lemmas true config)
def simpType (S : Expr → MetaM Simp.Result) (e : Expr) (type? : Option Expr := none) :
    MetaM Expr := do
  let type ← type?.getDM (inferType e)
  match ← S type with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'
def simpEq (S : Expr → MetaM Simp.Result) (type pf : Expr) : MetaM (Expr × Expr) := do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEqTrans (← mkEqSymm lhspf) pf'
    if let some rhspf := rhspf? then
      pf' ← mkEqTrans pf' rhspf
    let type' := mkApp3 (mkConst ``Eq [u]) α lhs' rhs'
    return (← mkForallFVars fvars type', ← mkLambdaFVars fvars pf')
def SimpTheorems.contains (d : SimpTheorems) (declName : Name) :=
  d.isLemma (.decl declName) || d.isDeclToUnfold declName
def isInSimpSet (simpAttr decl : Name) : CoreM Bool := do
  let .some simpDecl ← getSimpExtension? simpAttr | return false
  return (← simpDecl.getTheorems).contains decl
def getAllSimpDecls (simpAttr : Name) : CoreM (List Name) := do
  let .some simpDecl ← getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl => some decl
    | _ => none
def getAllSimpAttrs (decl : Name) : CoreM (Array Name) := do
  let mut simpAttrs := #[]
  for (simpAttr, simpDecl) in (← simpExtensionMapRef.get).toList do
    if (← simpDecl.getTheorems).contains decl then
      simpAttrs := simpAttrs.push simpAttr
  return simpAttrs
end Lean.Meta