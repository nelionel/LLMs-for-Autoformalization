import Mathlib.Algebra.Group.Pointwise.Finset.Basic
open MulOpposite
open Pointwise
variable {α : Type*} [DecidableEq α]
namespace Finset
section CommGroup
variable [CommGroup α] (e : α) (x : Finset α × Finset α)
@[to_additive (attr := simps) "The **Dyson e-transform**.
Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This reduces the sum of the two sets."]
def mulDysonETransform : Finset α × Finset α :=
  (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)
@[to_additive]
theorem mulDysonETransform.subset :
    (mulDysonETransform e x).1 * (mulDysonETransform e x).2 ⊆ x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [mul_smul_comm, smul_mul_assoc, inv_smul_smul, mul_comm]
@[to_additive]
theorem mulDysonETransform.card :
    (mulDysonETransform e x).1.card + (mulDysonETransform e x).2.card = x.1.card + x.2.card := by
  dsimp
  rw [← card_smul_finset e (_ ∩ _), smul_finset_inter, smul_inv_smul, inter_comm,
    card_union_add_card_inter, card_smul_finset]
@[to_additive (attr := simp)]
theorem mulDysonETransform_idem :
    mulDysonETransform e (mulDysonETransform e x) = mulDysonETransform e x := by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left]
    exact inter_subset_union
variable {e x}
@[to_additive]
theorem mulDysonETransform.smul_finset_snd_subset_fst :
    e • (mulDysonETransform e x).2 ⊆ (mulDysonETransform e x).1 := by
  dsimp
  rw [smul_finset_inter, smul_inv_smul, inter_comm]
  exact inter_subset_union
end CommGroup
section Group
variable [Group α] (e : α) (x : Finset α × Finset α)
@[to_additive (attr := simps) "An **e-transform**.
Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This reduces the sum of the two sets."]
def mulETransformLeft : Finset α × Finset α :=
  (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)
@[to_additive (attr := simps) "An **e-transform**.
Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the sum of the two sets."]
def mulETransformRight : Finset α × Finset α :=
  (x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)
@[to_additive (attr := simp)]
theorem mulETransformLeft_one : mulETransformLeft 1 x = x := by simp [mulETransformLeft]
@[to_additive (attr := simp)]
theorem mulETransformRight_one : mulETransformRight 1 x = x := by simp [mulETransformRight]
@[to_additive]
theorem mulETransformLeft.fst_mul_snd_subset :
    (mulETransformLeft e x).1 * (mulETransformLeft e x).2 ⊆ x.1 * x.2 := by
  refine inter_mul_union_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
@[to_additive]
theorem mulETransformRight.fst_mul_snd_subset :
    (mulETransformRight e x).1 * (mulETransformRight e x).2 ⊆ x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
@[to_additive]
theorem mulETransformLeft.card :
    (mulETransformLeft e x).1.card + (mulETransformRight e x).1.card = 2 * x.1.card :=
  (card_inter_add_card_union _ _).trans <| by rw [card_smul_finset, two_mul]
@[to_additive]
theorem mulETransformRight.card :
    (mulETransformLeft e x).2.card + (mulETransformRight e x).2.card = 2 * x.2.card :=
  (card_union_add_card_inter _ _).trans <| by rw [card_smul_finset, two_mul]
@[to_additive AddETransform.card "This statement is meant to be combined with
`le_or_lt_of_add_le_add` and similar lemmas."]
protected theorem MulETransform.card :
    (mulETransformLeft e x).1.card + (mulETransformLeft e x).2.card +
        ((mulETransformRight e x).1.card + (mulETransformRight e x).2.card) =
      x.1.card + x.2.card + (x.1.card + x.2.card) := by
  rw [add_add_add_comm, mulETransformLeft.card, mulETransformRight.card, ← mul_add, two_mul]
end Group
section CommGroup
variable [CommGroup α] (e : α) (x : Finset α × Finset α)
@[to_additive (attr := simp)]
theorem mulETransformLeft_inv : mulETransformLeft e⁻¹ x = (mulETransformRight e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]
@[to_additive (attr := simp)]
theorem mulETransformRight_inv : mulETransformRight e⁻¹ x = (mulETransformLeft e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]
end CommGroup
end Finset