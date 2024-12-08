import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
open CategoryTheory CategoryTheory.Limits
universe u v
namespace ModuleCat
variable {R : Type u} [Ring R]
section
variable {M N : ModuleCat.{v} R} (f : M ⟶ N)
def kernelCone : KernelFork f :=
  KernelFork.ofι (ofHom f.ker.subtype) <| by ext x; cases x; assumption
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s =>
      LinearMap.codRestrict (LinearMap.ker f) (Fork.ι s) fun c =>
        LinearMap.mem_ker.2 <| by
          erw [← @Function.comp_apply _ _ _ f (Fork.ι s) c, ← coe_comp]
          rw [Fork.condition, HasZeroMorphisms.comp_zero (Fork.ι s) N]
          rfl)
    (fun _ => LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
    LinearMap.ext fun x => Subtype.ext_iff_val.2 (by simp [← h]; rfl)
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (ofHom f.range.mkQ) <| LinearMap.range_mkQ_comp _
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s =>
      f.range.liftQ (Cofork.π s) <| LinearMap.range_le_ker_iff.2 <| CokernelCofork.condition s)
    (fun s => f.range.liftQ_mkQ (Cofork.π s) _) fun s m h => by
    haveI : Epi (ofHom (LinearMap.range f).mkQ) :=
      (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    apply (cancel_epi (ofHom (LinearMap.range f).mkQ)).1
    convert h
end
theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩
theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩
open ModuleCat
attribute [local instance] hasKernels_moduleCat
attribute [local instance] hasCokernels_moduleCat
variable {G H : ModuleCat.{v} R} (f : G ⟶ H)
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    kernel f ≅ ModuleCat.of R (LinearMap.ker f) :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩
@[simp, elementwise]
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f =
    (LinearMap.ker f).subtype :=
  limit.isoLimitCone_inv_π _ _
@[simp, elementwise]
theorem kernelIsoKer_hom_ker_subtype :
    (kernelIsoKer f).hom ≫ (LinearMap.ker f).subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    cokernel f ≅ ModuleCat.of R (H ⧸ LinearMap.range f) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩
@[simp, elementwise]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = f.range.mkQ :=
  colimit.isoColimitCocone_ι_hom _ _
@[simp, elementwise]
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ↿f.range.mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one
theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simpa only [map_add, add_right_eq_self] using cokernel.condition_apply f m
end ModuleCat