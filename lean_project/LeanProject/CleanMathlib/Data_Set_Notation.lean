import Mathlib.Util.Notation3
import Mathlib.Lean.Expr.ExtraRecognizers
namespace Set.Notation
scoped notation3 A:67 " ↓∩ " B:67 => (Subtype.val ⁻¹' (B : type_of% A) : Set (A : Set _))
instance {α : Type*} {s : Set α} : CoeHead (Set s) (Set α) := ⟨fun t => (Subtype.val '' t)⟩
open Lean PrettyPrinter Delaborator SubExpr in
@[scoped delab app.Set.image]
def delab_set_image_subtype : Delab := whenPPOption getPPCoercions do
  let #[α, _, f, _] := (← getExpr).getAppArgs | failure
  guard <| f.isAppOfArity ``Subtype.val 2
  let some _ := α.coeTypeSet? | failure
  let e ← withAppArg delab
  `(↑$e)
end Set.Notation