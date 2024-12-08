import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
suppress_compilation
universe v w x u
open CategoryTheory Opposite
namespace ModuleCat
variable {R : Type u} [CommRing R]
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun f := LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f)
  invFun f := (β_ M N).hom ≫ TensorProduct.lift f
  left_inv f := by
    apply TensorProduct.ext'
    intro m n
    erw [coe_comp]
    rw [Function.comp_apply]
    erw [MonoidalCategory.braiding_hom_apply, TensorProduct.lift.tmul]
  right_inv _ := rfl
instance : MonoidalClosed (ModuleCat.{u} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              homEquiv_naturality_left_symm := by
                intros
                apply TensorProduct.ext'
                intro m n
                rfl } }
theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl
open MonoidalCategory
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    @DFunLike.coe _ _ _ LinearMap.instFunLike
      ((MonoidalClosed.curry f : N →ₗ[R] M →ₗ[R] P) y) x = f (x ⊗ₜ[R] y) :=
  rfl
@[simp]
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) =
      @DFunLike.coe _ _ _ LinearMap.instFunLike (f y) x :=
  rfl
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = TensorProduct.uncurry _ _ _ _ LinearMap.id.flip := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = (TensorProduct.mk _ _ _).flip :=
  rfl
theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = LinearMap.lcomp R _ f :=
  rfl
end ModuleCat