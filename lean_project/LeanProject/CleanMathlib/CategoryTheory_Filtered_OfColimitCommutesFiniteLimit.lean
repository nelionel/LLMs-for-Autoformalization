import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Yoneda
universe v u
namespace CategoryTheory
variable {K : Type v} [SmallCategory K]
open Limits
theorem isFiltered_of_nonempty_limit_colimit_to_colimit_limit
    (h : ∀ {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ K ⥤ Type v),
      Nonempty (limit (colimit F.flip) ⟶ colimit (limit F))) : IsFiltered K := by
  refine IsFiltered.iff_nonempty_limit.2 (fun {J} _ _ F => ?_)
  suffices Nonempty (limit (colimit (F.op ⋙ coyoneda).flip)) by
    obtain ⟨X, y, -⟩ := Types.jointly_surjective' (this.map (h (F.op ⋙ coyoneda)).some).some
    exact ⟨X, ⟨(limitObjIsoLimitCompEvaluation (F.op ⋙ coyoneda) _).hom y⟩⟩
  let _ (j : Jᵒᵖ) : Unique ((colimit (F.op ⋙ coyoneda).flip).obj j) :=
    ((colimitObjIsoColimitCompEvaluation (F.op ⋙ coyoneda).flip _ ≪≫
      Coyoneda.colimitCoyonedaIso _)).toEquiv.unique
  exact ⟨Types.Limit.mk (colimit (F.op ⋙ coyoneda).flip) (fun j => default) (by subsingleton)⟩
end CategoryTheory