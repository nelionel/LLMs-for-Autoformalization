import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Order.CompleteLattice
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
namespace Functor
open Category Opposite Limits
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
def LeftAdjointObjIsDefined (X : C) : Prop := IsCorepresentable (F ⋙ coyoneda.obj (op X))
lemma leftAdjointObjIsDefined_iff (X : C) :
    F.LeftAdjointObjIsDefined X ↔ IsCorepresentable (F ⋙ coyoneda.obj (op X)) := by rfl
variable {F} in
lemma leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) :
    F.LeftAdjointObjIsDefined X :=
  (adj.corepresentableBy X).isCorepresentable
abbrev PartialLeftAdjointSource := FullSubcategory F.LeftAdjointObjIsDefined
instance (X : F.PartialLeftAdjointSource) :
    IsCorepresentable (F ⋙ coyoneda.obj (op X.obj)) := X.property
noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX
noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv
lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp
noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f ≫ F.partialLeftAdjointHomEquiv (𝟙 _))
@[simp]
lemma partialLeftAdjointHomEquiv_map {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) =
      by exact f ≫ F.partialLeftAdjointHomEquiv (𝟙 _) := by
  simp [partialLeftAdjointMap]
lemma partialLeftAdjointHomEquiv_map_comp {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X ⟶ X') (g : F.partialLeftAdjointObj X' ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f ≫ g) =
      by exact f ≫ F.partialLeftAdjointHomEquiv g := by
  rw [partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map, assoc,
    ← partialLeftAdjointHomEquiv_comp, id_comp]
@[simps]
noncomputable def partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where
  obj := F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    dsimp
    rw [partialLeftAdjointHomEquiv_map]
    erw [id_comp]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    dsimp
    rw [partialLeftAdjointHomEquiv_map, partialLeftAdjointHomEquiv_comp,
      partialLeftAdjointHomEquiv_map, assoc]
    erw [assoc]
    rw [← F.partialLeftAdjointHomEquiv_comp, id_comp,
      partialLeftAdjointHomEquiv_map]
variable {F}
lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (h : F.LeftAdjointObjIsDefined = ⊤) : F.IsRightAdjoint := by
  replace h : ∀ X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X ↦ by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y ↦ (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f ↦ by apply CorepresentableBy.homEquiv_comp)).isRightAdjoint
variable (F) in
lemma isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top :
    F.IsRightAdjoint ↔ F.LeftAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h ↦ ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X
noncomputable def corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category J]
    {R : J ⥤ F.PartialLeftAdjointSource}
    {c : Cocone (R ⋙ fullSubcategoryInclusion _)} (hc : IsColimit c)
    {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') :
    (F ⋙ coyoneda.obj (op c.pt)).CorepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f ↦ hc.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ ↦ by
            dsimp
            rw [comp_id, ← c'.w φ, ← partialLeftAdjointHomEquiv_map_comp, assoc]
            dsimp })
      invFun := fun g ↦ hc'.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv.symm (c.ι.app j ≫ g)
          naturality := fun j j' φ ↦ by
            apply F.partialLeftAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [comp_id, Equiv.apply_symm_apply, partialLeftAdjointHomEquiv_map_comp,
              Equiv.apply_symm_apply, reassoc_of% this] })
      left_inv := fun f ↦ hc'.hom_ext (fun j ↦ by simp)
      right_inv := fun g ↦ hc.hom_ext (fun j ↦ by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j ↦ by
    dsimp
    simp only [IsColimit.fac, IsColimit.fac_assoc, partialLeftAdjointHomEquiv_comp,
      F.map_comp, assoc] )
lemma leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.LeftAdjointObjIsDefined (R.obj j)) :
    F.LeftAdjointObjIsDefined c.pt :=
  (corepresentableByCompCoyonedaObjOfIsColimit
    (R := FullSubcategory.lift _ R h) hc (colimit.isColimit _)).isCorepresentable
lemma leftAdjointObjIsDefined_colimit {J : Type*} [Category J] (R : J ⥤ C)
    [HasColimit R] [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.LeftAdjointObjIsDefined (R.obj j)) :
    F.LeftAdjointObjIsDefined (colimit R) :=
  leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h
end Functor
end CategoryTheory