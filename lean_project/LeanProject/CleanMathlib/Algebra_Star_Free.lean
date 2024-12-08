import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.FreeAlgebra
namespace FreeMonoid
variable {α : Type*}
instance : StarMul (FreeMonoid α) where
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := List.reverse_append
@[simp]
theorem star_of (x : α) : star (of x) = of x :=
  rfl
@[simp]
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl
end FreeMonoid
namespace FreeAlgebra
variable {R : Type*} [CommSemiring R] {X : Type*}
instance : StarRing (FreeAlgebra R X) where
  star := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    unfold Star.star
    simp only [Function.comp_apply]
    let y := lift R (X := X) (MulOpposite.op ∘ ι R)
    refine induction (C := fun x ↦ (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
    · intros
      simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    · intros
      simp only [y, lift_ι_apply, Function.comp_apply, MulOpposite.unop_op]
    · intros
      simp only [*, map_mul, MulOpposite.unop_mul]
    · intros
      simp only [*, map_add, MulOpposite.unop_add]
  star_mul a b := by simp only [Function.comp_apply, map_mul, MulOpposite.unop_mul]
  star_add a b := by simp only [Function.comp_apply, map_add, MulOpposite.unop_add]
@[simp]
theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]
@[simp]
theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }
end FreeAlgebra