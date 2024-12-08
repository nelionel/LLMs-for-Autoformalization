import Mathlib.CategoryTheory.Limits.Shapes.Kernels
noncomputable section
universe v u
open CategoryTheory
open CategoryTheory.Limits
namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]
variable {P Q : C} (f : P ⟶ Q)
section Image
protected abbrev image : C :=
  kernel (cokernel.π f)
protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)
protected abbrev factorThruImage : P ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) f <| cokernel.condition f
protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _
instance mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f) :=
  mono_of_mono_fac <| image.fac f
end Image
section Coimage
protected abbrev coimage : C :=
  cokernel (kernel.ι f)
protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f <| kernel.condition f
protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _
instance epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f) :=
  epi_of_epi_fac <| coimage.fac f
end Coimage
def coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)
theorem coimageImageComparison_eq_coimageImageComparison' :
    coimageImageComparison f = coimageImageComparison' f := by
  ext
  simp [coimageImageComparison, coimageImageComparison']
@[reassoc (attr := simp)]
theorem coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f := by
  simp [coimageImageComparison]
end CategoryTheory.Abelian