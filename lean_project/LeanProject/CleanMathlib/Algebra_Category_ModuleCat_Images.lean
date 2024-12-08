import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images
open CategoryTheory
open CategoryTheory.Limits
universe u v
namespace ModuleCat
variable {R : Type u} [Ring R]
variable {G H : ModuleCat.{v} R} (f : G ⟶ H)
attribute [local ext] Subtype.ext_val
section
def image : ModuleCat R :=
  ModuleCat.of R (LinearMap.range f)
def image.ι : image f ⟶ H :=
  f.range.subtype
instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective
def factorThruImage : G ⟶ image f :=
  f.rangeRestrict
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  rfl
attribute [local simp] image.fac
variable {f}
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
  map_add' x y := by
    apply (mono_iff_injective F'.m).1
    · infer_instance
    rw [LinearMap.map_add]
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
    rfl
  map_smul' c x := by
    apply (mono_iff_injective F'.m).1
    · infer_instance
    rw [LinearMap.map_smul]
    change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
    simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
    rfl
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl
end
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac
noncomputable def imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f) :=
  IsImage.isoExt (Image.isImage f) (isImage f)
@[simp, reassoc, elementwise]
theorem imageIsoRange_inv_image_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCat.ofHom f.range.subtype :=
  IsImage.isoExt_inv_m _ _
@[simp, reassoc, elementwise]
theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).hom ≫ ModuleCat.ofHom f.range.subtype = Limits.image.ι f := by
  rw [← imageIsoRange_inv_image_ι f, Iso.hom_inv_id_assoc]
end ModuleCat