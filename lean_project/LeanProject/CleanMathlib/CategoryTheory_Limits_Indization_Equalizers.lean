import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
universe v v' u u'
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C]
section
variable {I : Type v} [SmallCategory I] [IsFiltered I]
variable {J : Type} [SmallCategory J] [FinCategory J]
variable (F : J ⥤ I ⥤ C)
theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)
end
end CategoryTheory.Limits