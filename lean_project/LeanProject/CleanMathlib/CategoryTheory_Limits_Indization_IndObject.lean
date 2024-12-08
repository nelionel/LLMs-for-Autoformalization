import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Filtered.Small
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
universe v v' u u'
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C]
structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  I : Type v
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  F : I ⥤ C
  ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
  isColimit : IsColimit (Cocone.mk A ι)
namespace IndObjectPresentation
@[simps]
def ofCocone {I : Type v} [SmallCategory I] [IsFiltered I] {F : I ⥤ C}
    (c : Cocone (F ⋙ yoneda)) (hc : IsColimit c) : IndObjectPresentation c.pt where
  I := I
  F := F
  ι := c.ι
  isColimit := hc
variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)
instance : SmallCategory P.I := P.ℐ
instance : IsFiltered P.I := P.hI
@[simps pt]
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit
@[simps!]
noncomputable def extend {A B : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) (η : A ⟶ B) [IsIso η] :
    IndObjectPresentation B :=
  .ofCocone (P.cocone.extend η) (P.coconeIsColimit.extendIso (by exact η))
@[simps! obj_left obj_right_as obj_hom map_left]
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _
instance : P.toCostructuredArrow.Final :=
  Presheaf.final_toCostructuredArrow_comp_pre _ P.coconeIsColimit
@[simps]
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun _ => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun _ _ h => h ⟨PUnit.unit⟩ }
end IndObjectPresentation
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)
theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
  .mk <| IndObjectPresentation.yoneda X
namespace IsIndObject
variable {A : Cᵒᵖ ⥤ Type v}
theorem map {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] : IsIndObject A → IsIndObject B
  | ⟨⟨P⟩⟩ => ⟨⟨P.extend η⟩⟩
theorem iff_of_iso {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] : IsIndObject A ↔ IsIndObject B :=
  ⟨.map η, .map (inv η)⟩
instance : ClosedUnderIsomorphisms (IsIndObject (C := C)) where
  of_iso i h := h.map i.hom
noncomputable def presentation : IsIndObject A → IndObjectPresentation A
  | ⟨P⟩ => P.some
theorem isFiltered (h : IsIndObject A) : IsFiltered (CostructuredArrow yoneda A) :=
  IsFiltered.of_final h.presentation.toCostructuredArrow
theorem finallySmall (h : IsIndObject A) : FinallySmall.{v} (CostructuredArrow yoneda A) :=
  FinallySmall.mk' h.presentation.toCostructuredArrow
end IsIndObject
open IsFiltered.SmallFilteredIntermediate
theorem isIndObject_of_isFiltered_of_finallySmall (A : Cᵒᵖ ⥤ Type v)
    [IsFiltered (CostructuredArrow yoneda A)] [FinallySmall.{v} (CostructuredArrow yoneda A)] :
    IsIndObject A := by
  have h₁ : (factoring (fromFinalModel (CostructuredArrow yoneda A)) ⋙
      inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final := Functor.final_of_natIso
    (factoringCompInclusion (fromFinalModel <| CostructuredArrow yoneda A)).symm
  have h₂ : Functor.Final (inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
    Functor.final_of_comp_full_faithful' (factoring _) (inclusion _)
  let c := (Presheaf.tautologicalCocone A).whisker
    (inclusion (fromFinalModel (CostructuredArrow yoneda A)))
  let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm
    (Presheaf.isColimitTautologicalCocone A)
  have hq : Nonempty (FinalModel (CostructuredArrow yoneda A)) := Nonempty.map
    (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
  exact ⟨_, inclusion (fromFinalModel _) ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩
theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) : IsIndObject A ↔
    (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) :=
  ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩
theorem isIndObject_limit_comp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F] :
    IsIndObject (limit (F ⋙ yoneda)) :=
  IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))
end CategoryTheory.Limits