import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
namespace CategoryTheory
open Category Bicategory
open Bicategory
universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃
variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    aesop_cat
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    aesop_cat
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    aesop_cat
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    aesop_cat
initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)
namespace Pseudofunctor
attribute [simp, reassoc, to_app]
  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor
section
open Iso
add_decl_doc Pseudofunctor.toPrelaxFunctor
attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor
variable (F : Pseudofunctor B C)
@[simps]
def toOplax : OplaxFunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom
instance hasCoeToOplax : Coe (Pseudofunctor B C) (OplaxFunctor B C) :=
  ⟨toOplax⟩
@[simps]
def toLax : LaxFunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
instance hasCoeToLax : Coe (Pseudofunctor B C) (LaxFunctor B C) :=
  ⟨toLax⟩
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : Pseudofunctor B B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)
instance : Inhabited (Pseudofunctor B B) :=
  ⟨id B⟩
@[simps]
def comp (F : Pseudofunctor B C) (G : Pseudofunctor C D) : Pseudofunctor B D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)
  map₂_whisker_left f η := by dsimp; simp
  map₂_whisker_right η h := by dsimp; simp
  map₂_associator f g h := by dsimp; simp
  map₂_left_unitor f := by dsimp; simp
  map₂_right_unitor f := by dsimp; simp
section
variable (F : Pseudofunctor B C) {a b : B}
@[reassoc, to_app]
lemma mapComp_assoc_right_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv ≫
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom :=
  F.toOplax.mapComp_assoc_right _ _ _
@[reassoc, to_app]
lemma mapComp_assoc_left_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv :=
  F.toOplax.mapComp_assoc_left _ _ _
@[reassoc, to_app]
lemma mapComp_assoc_right_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv =
    (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
    (F.mapComp (f ≫ g) h).inv ≫ F.map₂ (α_ f g h).hom :=
  F.toLax.mapComp_assoc_right _ _ _
@[reassoc, to_app]
lemma mapComp_assoc_left_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv =
    (α_ (F.map f) (F.map g) (F.map h)).hom ≫ F.map f ◁ (F.mapComp g h).inv ≫
    (F.mapComp f (g ≫ h)).inv ≫ F.map₂ (α_ f g h).inv :=
  F.toLax.mapComp_assoc_left _ _ _
@[reassoc, to_app]
lemma mapComp_id_left_hom (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f := by
  simp
lemma mapComp_id_left (f : a ⟶ b) : (F.mapComp (𝟙 a) f) = F.map₂Iso (λ_ f) ≪≫
    (λ_ (F.map f)).symm ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm :=
  Iso.ext <| F.mapComp_id_left_hom f
@[reassoc, to_app]
lemma mapComp_id_left_inv (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv =
    (F.mapId a).hom ▷ F.map f ≫ (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv := by
  simp [mapComp_id_left]
lemma whiskerRightIso_mapId (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) =
    (F.mapComp (𝟙 a) f).symm ≪≫ F.map₂Iso (λ_ f) ≪≫ (λ_ (F.map f)).symm := by
  simp [mapComp_id_left]
@[reassoc, to_app]
lemma whiskerRight_mapId_hom (f : a ⟶ b) : (F.mapId a).hom ▷ F.map f =
    (F.mapComp (𝟙 a) f).inv ≫ F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv := by
  simp [whiskerRightIso_mapId]
@[reassoc, to_app]
lemma whiskerRight_mapId_inv (f : a ⟶ b) : (F.mapId a).inv ▷ F.map f =
    (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv ≫ (F.mapComp (𝟙 a) f).hom := by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)
@[reassoc, to_app]
lemma mapComp_id_right_hom (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv := by
  simp
lemma mapComp_id_right (f : a ⟶ b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
    (ρ_ (F.map f)).symm ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm :=
  Iso.ext <| F.mapComp_id_right_hom f
@[reassoc, to_app]
lemma mapComp_id_right_inv (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv =
    F.map f ◁ (F.mapId b).hom ≫ (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv := by
  simp [mapComp_id_right]
lemma whiskerLeftIso_mapId (f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) =
    (F.mapComp f (𝟙 b)).symm ≪≫ F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm := by
  simp [mapComp_id_right]
@[reassoc, to_app]
lemma whiskerLeft_mapId_hom (f : a ⟶ b) : F.map f ◁ (F.mapId b).hom =
    (F.mapComp f (𝟙 b)).inv ≫ F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  simp [whiskerLeftIso_mapId]
@[reassoc, to_app]
lemma whiskerLeft_mapId_inv (f : a ⟶ b) : F.map f ◁ (F.mapId b).inv =
    (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom := by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)
end
@[simps]
def mkOfOplax (F : OplaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [F'.mapCompIso_hom f g, ← F.mapComp_naturality_right_assoc, ← F'.mapCompIso_hom f h,
      hom_inv_id, comp_id]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [F'.mapCompIso_hom _ h, ← F.mapComp_naturality_left_assoc, ← F'.mapCompIso_hom _ h,
      hom_inv_id, comp_id]
  map₂_associator := fun f g h => by
    dsimp
    rw [F'.mapCompIso_hom (f ≫ g) h, F'.mapCompIso_hom f g, ← F.map₂_associator_assoc, ←
      F'.mapCompIso_hom f (g ≫ h), ← F'.mapCompIso_hom g h, whiskerLeft_hom_inv_assoc,
      hom_inv_id, comp_id]
@[simps!]
noncomputable def mkOfOplax' (F : OplaxFunctor B C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv, ← inv_whiskerLeft, IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]
@[simps]
def mkOfLax (F : LaxFunctor B C) (F' : F.PseudoCore) : Pseudofunctor B C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_right, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_left, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv, F'.mapCompIso_inv, ← inv_comp_eq, ← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
@[simps!]
noncomputable def mkOfLax' (F : LaxFunctor B C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : Pseudofunctor B C :=
  mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }
end
end Pseudofunctor
end CategoryTheory