import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
namespace CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
section
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]
@[simps]
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]
@[simps]
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp, α.naturality]
variable (C D E)
@[simps]
def whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  obj F :=
    { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }
@[simps]
def whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  obj H :=
    { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }
variable {C} {D} {E}
instance faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] :
    ((whiskeringRight C D E).obj F).Faithful where
  map_injective hαβ := by
    ext X
    exact F.map_injective <| congr_fun (congr_arg NatTrans.app hαβ) X
@[simps]
def Functor.FullyFaithful.whiskeringRight {F : D ⥤ E} (hF : F.FullyFaithful)
    (C : Type*) [Category C] :
    ((whiskeringRight C D E).obj F).FullyFaithful where
  preimage f :=
    { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        dsimp
        simp only [map_comp, map_preimage]
        apply f.naturality }
theorem whiskeringLeft_obj_id : (whiskeringLeft C C E).obj (𝟭 _) = 𝟭 _ :=
  rfl
def whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _
theorem whiskeringLeft_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) =
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  rfl
def whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) ≅
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  Iso.refl _
theorem whiskeringRight_obj_id : (whiskeringRight E C C).obj (𝟭 _) = 𝟭 _ :=
  rfl
def wiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _
theorem whiskeringRight_obj_comp {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G =
    (whiskeringRight E C D').obj (F ⋙ G) :=
  rfl
def whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅
    (whiskeringRight E C D').obj (F ⋙ G) :=
  Iso.refl _
instance full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] :
    ((whiskeringRight C D E).obj F).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full
@[simp]
theorem whiskerLeft_id (F : C ⥤ D) {G : D ⥤ E} :
    whiskerLeft F (NatTrans.id G) = NatTrans.id (F.comp G) :=
  rfl
@[simp]
theorem whiskerLeft_id' (F : C ⥤ D) {G : D ⥤ E} : whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  rfl
@[simp]
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _
@[simp]
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _
@[simp, reassoc]
theorem whiskerLeft_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β :=
  rfl
@[simp, reassoc]
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β
def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α
@[simp]
theorem isoWhiskerLeft_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).hom = whiskerLeft F α.hom :=
  rfl
@[simp]
theorem isoWhiskerLeft_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
    (isoWhiskerLeft F α).inv = whiskerLeft F α.inv :=
  rfl
def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α
@[simp]
theorem isoWhiskerRight_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).hom = whiskerRight α.hom F :=
  rfl
@[simp]
theorem isoWhiskerRight_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    (isoWhiskerRight α F).inv = whiskerRight α.inv F :=
  rfl
instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  (isoWhiskerLeft F (asIso α)).isIso_hom
instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  (isoWhiskerRight (asIso α) F).isIso_hom
variable {B : Type u₄} [Category.{v₄} B]
attribute [elab_without_expected_type] whiskerLeft whiskerRight
@[simp]
theorem whiskerLeft_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) = whiskerLeft (F ⋙ G) α :=
  rfl
@[simp]
theorem whiskerRight_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
    whiskerRight (whiskerRight α F) G = whiskerRight α (F ⋙ G) :=
  rfl
theorem whiskerRight_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
    whiskerRight (whiskerLeft F α) K = whiskerLeft F (whiskerRight α K) :=
  rfl
end
namespace Functor
universe u₅ v₅
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
@[simps]
def leftUnitor (F : A ⥤ B) :
    𝟭 A ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }
@[simps]
def rightUnitor (F : A ⥤ B) :
    F ⋙ 𝟭 B ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
@[simps]
def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
protected theorem assoc (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  rfl
theorem triangle (F : A ⥤ B) (G : B ⥤ C) :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by aesop_cat
variable {E : Type u₅} [Category.{v₅} E]
variable (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)
theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by aesop_cat
end Functor
end CategoryTheory