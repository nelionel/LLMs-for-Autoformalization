import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.Products
universe v u
namespace CategoryTheory
@[nolint checkUnivs]
def Grpd :=
  Bundled Groupoid.{v, u}
namespace Grpd
instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩
instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str
instance : CoeSort Grpd Type* :=
  Bundled.coeSort
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C
@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl
instance category : LargeCategory.{max v u} Grpd.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc := by intros; rfl
def objects : Grpd.{v, u} ⥤ Type u where
  obj := Bundled.α
  map F := F.obj
def forgetToCat : Grpd.{v, u} ⥤ Cat.{v, u} where
  obj C := Cat.of C
  map := id
instance forgetToCat_full : forgetToCat.Full where map_surjective f := ⟨f, rfl⟩
instance forgetToCat_faithful : forgetToCat.Faithful where
theorem hom_to_functor {C D E : Grpd.{v, u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g :=
  rfl
theorem id_to_functor {C : Grpd.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl
section Products
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [hom_to_functor])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)
instance has_pi : Limits.HasProducts.{u} Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)
noncomputable def piIsoPi (J : Type u) (f : J → Grpd.{u, u}) : @of (∀ j, f j) _ ≅ ∏ᶜ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))
@[simp]
theorem piIsoPi_hom_π (J : Type u) (f : J → Grpd.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl
end Products
end Grpd
end CategoryTheory