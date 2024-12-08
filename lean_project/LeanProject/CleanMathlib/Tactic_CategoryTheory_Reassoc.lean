import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Util.AddRelatedDecl
open Lean Meta Elab Tactic
open Mathlib.Tactic
namespace CategoryTheory
variable {C : Type*} [Category C]
theorem eq_whisker' {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by rw [w]
def categorySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Functor.id_obj, ``Functor.id_map, ``Functor.comp_obj, ``Functor.comp_map] e
    (config := { decide := false })
def reassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType categorySimp (← mkAppM ``eq_whisker' #[e])) e
syntax (name := reassoc) "reassoc" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr
initialize registerBuiltinAttribute {
  name := `reassoc
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| reassoc $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`reassoc` can only be used as a global attribute"
    addRelatedDecl src "_assoc" ref stx? fun type value levels => do
      pure (← reassocExpr (← mkExpectedTypeHint value type), levels)
  | _ => throwUnsupportedSyntax }
open Term in
elab "reassoc_of% " t:term : term => do
  reassocExpr (← elabTerm t none)
end CategoryTheory