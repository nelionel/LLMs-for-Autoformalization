import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic.CategoryTheory.Elementwise
open CategoryTheory
open CategoryTheory.Limits
universe u v w
namespace ModuleCat
variable {R : Type u} [Ring R]
variable {ι : Type v} (Z : ι → ModuleCatMax.{v, w} R)
section product
def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (∀ i : ι, Z i)) fun i => (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i)
def productConeIsLimit : IsLimit (productCone Z) where
  lift s := (LinearMap.pi fun j => s.π.app ⟨j⟩ : s.pt →ₗ[R] ∀ i : ι, Z i)
  fac s j := by
    cases j
    aesop
  uniq s m w := by
    ext x
    funext i
    exact LinearMap.congr_fun (w ⟨i⟩) x
variable [HasProduct Z]
noncomputable def piIsoPi : ∏ᶜ Z ≅ ModuleCat.of R (∀ i, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩
@[simp, elementwise]
theorem piIsoPi_inv_kernel_ι (i : ι) :
    (piIsoPi Z).inv ≫ Pi.π Z i = (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) :=
  limit.isoLimitCone_inv_π _ _
@[simp, elementwise]
theorem piIsoPi_hom_ker_subtype (i : ι) :
    (piIsoPi Z).hom ≫ (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) = Pi.π Z i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)
end product
section coproduct
open DirectSum
variable [DecidableEq ι]
def coproductCocone : Cofan Z :=
  Cofan.mk (ModuleCat.of R (⨁ i : ι, Z i)) fun i => (DirectSum.lof R ι (fun i ↦ Z i) i)
def coproductCoconeIsColimit : IsColimit (coproductCocone Z) where
  desc s := DirectSum.toModule R ι _ fun i ↦ s.ι.app ⟨i⟩
  fac := by
    rintro s ⟨i⟩
    ext (x : Z i)
    simpa only [Discrete.functor_obj_eq_as, coproductCocone, Cofan.mk_pt, Functor.const_obj_obj,
      Cofan.mk_ι_app, coe_comp, Function.comp_apply] using
      DirectSum.toModule_lof (ι := ι) R (M := fun i ↦ Z i) i x
  uniq := by
    rintro s f h
    refine DirectSum.linearMap_ext _ fun i ↦ ?_
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, toModule_lof] using
      congr($(h ⟨i⟩) x)
variable [HasCoproduct Z]
noncomputable def coprodIsoDirectSum : ∐ Z ≅ ModuleCat.of R (⨁ i, Z i) :=
  colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩
@[simp, elementwise]
theorem ι_coprodIsoDirectSum_hom (i : ι) :
    Sigma.ι Z i ≫ (coprodIsoDirectSum Z).hom = DirectSum.lof R ι (fun i ↦ Z i) i :=
  colimit.isoColimitCocone_ι_hom _ _
@[simp, elementwise]
theorem lof_coprodIsoDirectSum_inv (i : ι) :
    DirectSum.lof R ι (fun i ↦ Z i) i ≫ (coprodIsoDirectSum Z).inv = Sigma.ι Z i :=
  (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _
end coproduct
end ModuleCat