import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.SMulWithZero
open Function
variable {G G₀ A M M₀ N₀ R α : Type*}
section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ α] {a : G₀}
protected lemma MulAction.bijective₀ (ha : a ≠ 0) : Bijective (a • · : α → α) :=
  MulAction.bijective <| Units.mk0 a ha
protected lemma MulAction.injective₀ (ha : a ≠ 0) : Injective (a • · : α → α) :=
  (MulAction.bijective₀ ha).injective
protected lemma MulAction.surjective₀ (ha : a ≠ 0) : Surjective (a • · : α → α) :=
  (MulAction.bijective₀ ha).surjective
end GroupWithZero
section DistribMulAction
variable [Group G] [Monoid M] [AddMonoid A]
variable (A)
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where
  __ := toAddMonoidHom A x
  __ := MulAction.toPermHom G A x
variable (G)
@[simps]
def DistribMulAction.toAddAut [DistribMulAction G A] : G →* AddAut A where
  toFun := toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
end DistribMulAction
@[simps]
def smulMonoidWithZeroHom [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionWithZero M₀ N₀]
    [IsScalarTower M₀ N₀ N₀] [SMulCommClass M₀ N₀ N₀] : M₀ × N₀ →*₀ N₀ :=
  { smulMonoidHom with map_zero' := smul_zero _ }
section MulDistribMulAction
variable [Group G] [Monoid M] [MulDistribMulAction G M]
variable (M)
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }
variable (G)
@[simps]
def MulDistribMulAction.toMulAut : G →* MulAut M where
  toFun := MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)
end MulDistribMulAction
namespace MulAut
instance applyMulDistribMulAction [Monoid M] : MulDistribMulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one := map_one
  smul_mul := map_mul
end MulAut
namespace AddAut
instance applyDistribMulAction [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
end AddAut
section Arrow
variable [Group G] [MulAction G A] [Monoid M]
attribute [local instance] arrowAction
def arrowMulDistribMulAction : MulDistribMulAction G (A → M) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl
attribute [local instance] arrowMulDistribMulAction
@[simps!] def mulAutArrow : G →* MulAut (A → M) := MulDistribMulAction.toMulAut _ _
end Arrow
lemma IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
    [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) :
    IsUnit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]