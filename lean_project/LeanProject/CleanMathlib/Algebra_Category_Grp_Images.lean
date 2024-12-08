import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images
open CategoryTheory
open CategoryTheory.Limits
universe u
namespace AddCommGrp
variable {G H : AddCommGrp.{0}} (f : G ⟶ H)
attribute [local ext] Subtype.ext_val
section
def image : AddCommGrp :=
  AddCommGrp.of (AddMonoidHom.range f)
def image.ι : image f ⟶ H :=
  f.range.subtype
instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective
def factorThruImage : G ⟶ image f :=
  f.rangeRestrict
theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  rfl
attribute [local simp] image.fac
variable {f}
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
  map_zero' := by
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    change (F'.e ≫ F'.m) _ = _
    rw [F'.fac, AddMonoidHom.map_zero]
    exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
  map_add' := by
    intro x y
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    rw [AddMonoidHom.map_add]
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    rw [F'.fac]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
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
noncomputable def imageIsoRange {G H : AddCommGrp.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGrp.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)
end AddCommGrp