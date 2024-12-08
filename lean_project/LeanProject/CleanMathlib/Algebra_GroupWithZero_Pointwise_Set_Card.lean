import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.SetTheory.Cardinal.Finite
open scoped Cardinal Pointwise
variable {G₀ M₀ : Type*}
namespace Set
variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}
lemma _root_.Cardinal.mk_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn
lemma natCard_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective₀ ha) _
end Set