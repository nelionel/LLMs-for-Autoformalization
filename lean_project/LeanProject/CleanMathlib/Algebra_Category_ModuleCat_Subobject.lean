import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Subobject.Limits
open CategoryTheory
open CategoryTheory.Subobject
open CategoryTheory.Limits
open ModuleCat
universe v u
namespace ModuleCat
variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow
      toFun := fun N => Subobject.mk (↾N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso'Left
          apply LinearEquiv.ofBijective (LinearMap.codRestrict (LinearMap.range S.arrow) S.arrow _)
          constructor
          · simp [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
            rw [ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · apply LinearMap.ext
          intro x
          rfl)
      left_inv := fun N => by
        convert congr_arg LinearMap.range
            (underlyingIso_arrow (↾N.subtype : of R { x // x ∈ N } ⟶ M)) using 1
        · have :
            (underlyingIso (↾N.subtype : of R _ ⟶ M)).inv =
              (underlyingIso (↾N.subtype : of R _ ⟶ M)).symm.toLinearEquiv.toLinearMap := by
              apply LinearMap.ext
              intro x
              rfl
          rw [this, comp_def, LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert LinearMap.range_comp_le_range (ofMkLEMk _ _ h) (↾T.subtype)
        · simpa only [← comp_def, ofMkLEMk_comp] using (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }
instance wellPowered_moduleCat : WellPowered (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩
attribute [local instance] hasKernels_moduleCat
noncomputable def toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} :
    LinearMap.ker f →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv
@[simp]
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  suffices ((arrow ((kernelSubobject f))) ∘ (kernelSubobjectIso f ≪≫ kernelIsoKer f).inv) x = x by
    convert this
  rw [Iso.trans_inv, ← coe_comp, Category.assoc]
  simp only [Category.assoc, kernelSubobject_arrow', kernelIsoKer_inv_kernel_ι]
  aesop_cat
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  simp only [map_add, add_right_eq_self]
  change ((cokernel.π g) ∘ (g) ∘ (factorThruImageSubobject f)) l = 0
  rw [← coe_comp, ← coe_comp, Category.assoc]
  simp only [cokernel.condition, comp_zero]
  rfl
end ModuleCat