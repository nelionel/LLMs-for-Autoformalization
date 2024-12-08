import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.Over
namespace CategoryTheory
open Category Opposite Limits
universe w v u
variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}
variable {J : Type v} [SmallCategory J] {A : Cᵒᵖ ⥤ Type v} (F : J ⥤ Over A)
local notation "E" => Equivalence.functor (overEquivPresheafCostructuredArrow A)
local notation "E.obj" =>
  Prefunctor.obj (Functor.toPrefunctor (Equivalence.functor (overEquivPresheafCostructuredArrow A)))
noncomputable def CostructuredArrow.toOverCompYonedaColimit :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F) ≅
    (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) := calc
  (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F)
    ≅ yoneda.op ⋙ yoneda.obj (E.obj (colimit F)) :=
        CostructuredArrow.toOverCompYoneda A _
  _ ≅ yoneda.op ⋙ yoneda.obj (colimit (F ⋙ E)) :=
        isoWhiskerLeft yoneda.op (yoneda.mapIso (preservesColimitIso _ F))
  _ ≅ yoneda.op ⋙ colimit ((F ⋙ E) ⋙ yoneda) :=
        yonedaYonedaColimit _
  _ ≅ yoneda.op ⋙ ((F ⋙ E) ⋙ yoneda).flip ⋙ colim :=
        isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj E) ⋙
          (whiskeringLeft _ _ _).obj F ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F ⋙ colim :=
        isoWhiskerRight (CostructuredArrow.toOverCompCoyoneda _).symm _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) :=
      isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm
end CategoryTheory