import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Elements
open CategoryTheory Limits
universe v u
namespace CategoryTheory.Limits
section LargeCategory
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type v)
theorem isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
    [PreservesFiniteLimits A] : IsFiltered (CostructuredArrow yoneda A) := by
  suffices IsCofiltered A.Elements from
    IsFiltered.of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
  suffices HasFiniteLimits A.Elements from IsCofiltered.of_hasFiniteLimits A.Elements
  exact ⟨fun J _ _ => inferInstance⟩
end LargeCategory
variable {C : Type u} [SmallCategory C] [HasFiniteColimits C]
variable (A : Cᵒᵖ ⥤ Type u)
namespace PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux
variable {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ Cᵒᵖ)
def functorToInterchange : J ⥤ CostructuredArrow yoneda A ⥤ Type u :=
  K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)
@[simps!]
def functorToInterchangeIso : functorToInterchange A K ≅
    K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _) :=
  Iso.refl _
@[simps!]
def flipFunctorToInterchange : (functorToInterchange A K).flip ≅
    ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft J Cᵒᵖ (Type u)).obj K) :=
  Iso.refl _
@[simps! (config := { fullyApplied := false }) hom_app]
noncomputable def isoAux :
    (CostructuredArrow.proj yoneda A ⋙ yoneda ⋙ (evaluation Cᵒᵖ (Type u)).obj (limit K)) ≅
      ((coyoneda ⋙ (whiskeringLeft (CostructuredArrow yoneda A) C (Type u)).obj
        (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
  Iso.refl _
noncomputable def iso [IsFiltered (CostructuredArrow yoneda A)] :
    A.obj (limit K) ≅ limit (K ⋙ A) := calc
  A.obj (limit K) ≅ (colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)).obj (limit K) :=
      (IsColimit.coconePointUniqueUpToIso
        (Presheaf.isColimitTautologicalCocone A) (colimit.isColimit _)).app _
  _ ≅ colimit (((CostructuredArrow.proj yoneda A) ⋙ yoneda) ⋙ (evaluation _ _).obj (limit K)) :=
      (colimitObjIsoColimitCompEvaluation _ _)
  _ ≅ colimit ((CostructuredArrow.proj yoneda A) ⋙ yoneda ⋙ (evaluation _ _).obj (limit K)) :=
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  _ ≅ colimit
      ((coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
        HasColimit.isoOfNatIso (isoAux A K)
  _ ≅ colimit (limit (K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)))) :=
        HasColimit.isoOfNatIso (preservesLimitIso _ _)
  _ ≅ colimit (limit (functorToInterchange A K)) :=
        HasColimit.isoOfNatIso (HasLimit.isoOfNatIso (functorToInterchangeIso A K).symm)
  _ ≅ limit (colimit (functorToInterchange A K).flip) := colimitLimitIso _
  _ ≅ limit (colimit
        ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj K)) :=
          HasLimit.isoOfNatIso (HasColimit.isoOfNatIso (flipFunctorToInterchange A K))
  _ ≅ limit (K ⋙ colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)) :=
        HasLimit.isoOfNatIso
          (colimitCompWhiskeringLeftIsoCompColimit (CostructuredArrow.proj yoneda A ⋙ yoneda) K)
  _ ≅ limit (K ⋙ A) := HasLimit.isoOfNatIso (isoWhiskerLeft _
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit _) (Presheaf.isColimitTautologicalCocone A)))
theorem iso_hom [IsFiltered (CostructuredArrow yoneda A)] : (iso A K).hom = limit.post K A := by
  dsimp [iso, -Iso.app_hom]
  simp only [Category.assoc]
  rw [Eq.comm, ← Iso.inv_comp_eq, ← Iso.inv_comp_eq]
  refine limit.hom_ext (fun j => colimit.hom_ext (fun i => ?_))
  simp only [Category.assoc]
  rw [HasLimit.isoOfNatIso_hom_π, HasLimit.isoOfNatIso_hom_π_assoc, limit.post_π,
    colimitObjIsoColimitCompEvaluation_ι_inv_assoc (CostructuredArrow.proj yoneda A ⋙ yoneda),
    Iso.app_inv, ← NatTrans.comp_app_assoc, colimit.comp_coconePointUniqueUpToIso_inv,
    Presheaf.tautologicalCocone_ι_app, HasColimit.isoOfNatIso_ι_hom_assoc,
    HasLimit.isoOfNatIso_hom_π_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    ι_colimitLimitIso_limit_π_assoc, isoAux_hom_app, ← NatTrans.comp_app_assoc,
    ← NatTrans.comp_app_assoc, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    preservesLimitIso_hom_π_assoc, Iso.symm_hom,
    ← NatTrans.comp_app_assoc, HasColimit.isoOfNatIso_ι_hom,
    ← NatTrans.comp_app_assoc, Category.assoc,
    ι_colimitCompWhiskeringLeftIsoCompColimit_hom,
    NatTrans.comp_app, Category.assoc, isoWhiskerLeft_hom, NatTrans.comp_app, Category.assoc,
    ← NatTrans.comp_app, ← whiskerLeft_comp, colimit.comp_coconePointUniqueUpToIso_hom]
  have := i.hom.naturality (limit.π K j)
  dsimp only [yoneda_obj_obj, Functor.const_obj_obj] at this
  rw [← this]
  ext
  simp
theorem isIso_post [IsFiltered (CostructuredArrow yoneda A)] : IsIso (limit.post K A) :=
  iso_hom A K ▸ inferInstance
end PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux
attribute [local instance] PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux.isIso_post
lemma preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    [IsFiltered (CostructuredArrow yoneda A)] : PreservesFiniteLimits A where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => preservesLimit_of_isIso_post _ _⟩
theorem isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits :
    IsFiltered (CostructuredArrow yoneda A) ↔ Nonempty (PreservesFiniteLimits A) :=
  ⟨fun _ => ⟨preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda A⟩,
   fun ⟨_⟩ => isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A⟩
end CategoryTheory.Limits