import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Subsemigroup.Defs
assert_not_exists Finset
variable (M)
namespace Subsemigroup
section Mul
variable [Mul M]
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center
variable {M}
@[to_additive "The center of an additive magma is commutative and associative."]
instance center.commSemigroup : CommSemigroup (center M) where
  mul_assoc _ b _ := Subtype.ext <| b.2.mid_assoc _ _
  mul_comm a _ := Subtype.ext <| a.2.comm _
end Mul
section Semigroup
variable {M} [Semigroup M]
@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] :
    Decidable (a ∈ center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff
end Semigroup
section CommSemigroup
variable [CommSemigroup M]
@[to_additive (attr := simp)]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
end CommSemigroup
end Subsemigroup