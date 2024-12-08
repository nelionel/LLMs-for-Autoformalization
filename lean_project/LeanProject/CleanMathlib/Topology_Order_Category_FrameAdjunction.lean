import Mathlib.Topology.Category.Locale
open CategoryTheory Order Set Topology TopologicalSpace
namespace Locale
section pt_definition
variable (L : Type*) [CompleteLattice L]
abbrev PT := FrameHom L Prop
@[simps]
def openOfElementHom : FrameHom L (Set (PT L)) where
  toFun u := {x | x u}
  map_inf' a b := by simp [Set.setOf_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists_iff]
namespace PT
instance instTopologicalSpace : TopologicalSpace (PT L) where
  IsOpen s := ∃ u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, setOf_exists, hf, sUnion_eq_biUnion]
lemma isOpen_iff (U : Set (PT L)) : IsOpen U ↔ ∃ u : L, {x | x u} = U := Iff.rfl
end PT
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike
def pt : Locale ⥤ TopCat where
  obj L := ⟨PT L.unop, inferInstance⟩
  map f := ⟨fun p ↦ p.comp f.unop, continuous_def.2 <| by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩
end pt_definition
section locale_top_adjunction
variable (X : Type*) [TopologicalSpace X] (L : Locale)
@[simps]
def localePointOfSpacePoint (x : X) : PT (Opens X) where
  toFun := (x ∈ ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]
def counitAppCont : FrameHom L (Opens <| PT L) where
  toFun u := ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp
def adjunctionTopToLocalePT : topToLocale ⊣ pt where
  unit := { app := fun X ↦ ⟨localePointOfSpacePoint X, continuous_def.2 <|
        by rintro _ ⟨u, rfl⟩; simpa using u.2⟩ }
  counit := { app := fun L ↦ ⟨counitAppCont L⟩ }
end locale_top_adjunction
end Locale