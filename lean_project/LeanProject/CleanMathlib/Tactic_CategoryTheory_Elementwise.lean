import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Util.AddRelatedDecl
import Batteries.Tactic.Lint
open Lean Meta Elab Tactic
open Mathlib.Tactic
namespace Tactic.Elementwise
open CategoryTheory
section theorems
universe u
theorem forall_congr_forget_Type (α : Type u) (p : α → Prop) :
    (∀ (x : (forget (Type u)).obj α), p x) ↔ ∀ (x : α), p x := Iff.rfl
attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort
theorem forget_hom_Type (α β : Type u) (f : α ⟶ β) : DFunLike.coe f = f := rfl
theorem hom_elementwise {C : Type*} [Category C] [ConcreteCategory C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x := by rw [h]
end theorems
def elementwiseThms : List Name :=
  [``CategoryTheory.coe_id, ``CategoryTheory.coe_comp, ``CategoryTheory.comp_apply,
    ``CategoryTheory.id_apply,
    ``forget_hom_Type, ``forall_congr_forget_Type,
    ``implies_true]
def elementwiseExpr (src : Name) (type pf : Expr) (simpSides := true) :
    MetaM (Expr × Option Level) := do
  let type := (← instantiateMVars type).cleanupAnnotations
  forallTelescope type fun fvars type' => do
    mkHomElementwise type' (← mkExpectedTypeHint (mkAppN pf fvars) type') fun eqPf instConcr? => do
      let mut eqPf' ← simpType (simpOnlyNames elementwiseThms (config := { decide := false })) eqPf
      if (← inferType eqPf') == .const ``True [] then
        throwError "elementwise lemma for {src} is trivial after applying ConcreteCategory \
          lemmas, which can be caused by how applications are unfolded. \
          Using elementwise is unnecessary."
      if simpSides then
        let ctx ← Simp.Context.mkDefault
        let (ty', eqPf'') ← simpEq (fun e => return (← simp e ctx).1) (← inferType eqPf') eqPf'
        forallTelescope ty' fun _ ty' => do
          if let some (_, lhs, rhs) := ty'.eq? then
            if ← Batteries.Tactic.Lint.isSimpEq lhs rhs then
              throwError "applying simp to both sides reduces elementwise lemma for {src} \
                to the trivial equality {ty'}. \
                Either add `nosimp` or remove the `elementwise` attribute."
        eqPf' ← mkExpectedTypeHint eqPf'' ty'
      if let some (w, instConcr) := instConcr? then
        return (← Meta.mkLambdaFVars (fvars.push instConcr) eqPf', w)
      else
        return (← Meta.mkLambdaFVars fvars eqPf', none)
where
  extractCatInstance (eqTy : Expr) : MetaM (Expr × Expr) := do
    let some (α, _, _) := eqTy.cleanupAnnotations.eq? | failure
    let (``Quiver.Hom, #[_, instQuiv, _, _]) := α.getAppFnArgs | failure
    let (``CategoryTheory.CategoryStruct.toQuiver, #[_, instCS]) := instQuiv.getAppFnArgs | failure
    let (``CategoryTheory.Category.toCategoryStruct, #[C, instC]) := instCS.getAppFnArgs | failure
    return (C, instC)
  mkHomElementwise {α} (eqTy eqPf : Expr) (k : Expr → Option (Level × Expr) → MetaM α) :
      MetaM α := do
    let (C, instC) ← try extractCatInstance eqTy catch _ =>
      throwError "elementwise expects equality of morphisms in a category"
    if let some eqPf' ← observing? (mkAppM ``hom_elementwise #[eqPf]) then
      k eqPf' none
    else
      let .app (.const ``Category [v, u]) _ ← inferType instC
        | throwError "internal error in elementwise"
      let w ← mkFreshLevelMVar
      let cty : Expr := mkApp2 (.const ``ConcreteCategory [w, v, u]) C instC
      withLocalDecl `inst .instImplicit cty fun cfvar => do
        let eqPf' ← mkAppM ``hom_elementwise #[eqPf]
        k eqPf' (some (w, cfvar))
private partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    let rec loop (i : Nat := 0) : Name :=
      let w := Name.appendIndexAfter baseName i
      if names.contains w then
        loop (i + 1)
      else
        w
    loop 1
syntax (name := elementwise) "elementwise"
  " nosimp"? (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr
initialize registerBuiltinAttribute {
  name := `elementwise
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| elementwise $[nosimp%$nosimp?]? $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`elementwise` can only be used as a global attribute"
    addRelatedDecl src "_apply" ref stx? fun type value levels => do
      let (newValue, level?) ← elementwiseExpr src type value (simpSides := nosimp?.isNone)
      let newLevels ← if let some level := level? then do
        let w := mkUnusedName levels `w
        unless ← isLevelDefEq level (mkLevelParam w) do
          throwError "Could not create level parameter for ConcreteCategory instance"
        pure <| w :: levels
      else
        pure levels
      pure (newValue, newLevels)
  | _ => throwUnsupportedSyntax }
elab "elementwise_of% " t:term : term => do
  let e ← Term.elabTerm t none
  let (pf, _) ← elementwiseExpr .anonymous (← inferType e) e (simpSides := false)
  return pf
syntax "elementwise" (ppSpace colGt ident)* : tactic
syntax "elementwise!" (ppSpace colGt ident)* : tactic
end Tactic.Elementwise