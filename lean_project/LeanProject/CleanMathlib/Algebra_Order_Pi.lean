import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Pi
variable {I α β γ : Type*}
variable {f : I → Type*}
namespace Pi
@[to_additive
      "The product of a family of ordered additive commutative monoids is
an ordered additive commutative monoid."]
instance orderedCommMonoid {ι : Type*} {Z : ι → Type*} [∀ i, OrderedCommMonoid (Z i)] :
    OrderedCommMonoid (∀ i, Z i) where
  __ := Pi.partialOrder
  __ := Pi.commMonoid
  mul_le_mul_left _ _ w _ := fun i => mul_le_mul_left' (w i) _
@[to_additive]
instance existsMulOfLe {ι : Type*} {α : ι → Type*} [∀ i, LE (α i)] [∀ i, Mul (α i)]
    [∀ i, ExistsMulOfLE (α i)] : ExistsMulOfLE (∀ i, α i) :=
  ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩
@[to_additive
      "The product of a family of canonically ordered additive monoids is
a canonically ordered additive monoid."]
instance {ι : Type*} {Z : ι → Type*} [∀ i, CanonicallyOrderedCommMonoid (Z i)] :
    CanonicallyOrderedCommMonoid (∀ i, Z i) where
  __ := Pi.instOrderBot
  __ := Pi.orderedCommMonoid
  __ := Pi.existsMulOfLe
  le_self_mul _ _ := fun _ => le_self_mul
@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] :
    OrderedCancelCommMonoid (∀ i : I, f i) where
  __ := Pi.commMonoid
  le_of_mul_le_mul_left _ _ _ h i := le_of_mul_le_mul_left' (h i)
  mul_le_mul_left _ _ c h i := mul_le_mul_left' (c i) (h i)
@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) where
  __ := Pi.commGroup
  __ := Pi.orderedCommMonoid
  npow := Monoid.npow
instance orderedSemiring [∀ i, OrderedSemiring (f i)] : OrderedSemiring (∀ i, f i) where
  __ := Pi.semiring
  __ := Pi.partialOrder
  add_le_add_left _ _ hab _ := fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
  mul_le_mul_of_nonneg_left _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_left (hab _) <| hc _
  mul_le_mul_of_nonneg_right _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_right (hab _) <| hc _
instance orderedCommSemiring [∀ i, OrderedCommSemiring (f i)] : OrderedCommSemiring (∀ i, f i) where
  __ := Pi.commSemiring
  __ := Pi.orderedSemiring
instance orderedRing [∀ i, OrderedRing (f i)] : OrderedRing (∀ i, f i) where
  __ := Pi.ring
  __ := Pi.orderedSemiring
  mul_nonneg _ _ ha hb := fun _ => mul_nonneg (ha _) (hb _)
instance orderedCommRing [∀ i, OrderedCommRing (f i)] : OrderedCommRing (∀ i, f i) where
  __ := Pi.commRing
  __ := Pi.orderedRing
end Pi
namespace Function
section const
variable (β) [One α] [Preorder α] {a : α}
@[to_additive const_nonneg_of_nonneg]
theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha
@[to_additive]
theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha
variable {β} [Nonempty β]
@[to_additive (attr := simp) const_nonneg]
theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a :=
  const_le_const
@[to_additive (attr := simp) const_pos]
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  const_lt_const
@[to_additive (attr := simp)]
theorem const_le_one : const β a ≤ 1 ↔ a ≤ 1 :=
  const_le_const
@[to_additive (attr := simp) const_neg']
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  const_lt_const
end const
section extend
variable [One γ] [LE γ] {f : α → β} {g : α → γ} {e : β → γ}
@[to_additive extend_nonneg] lemma one_le_extend (hg : 1 ≤ g) (he : 1 ≤ e) : 1 ≤ extend f g e :=
  fun _b ↦ by classical exact one_le_dite (fun _ ↦ hg _) (fun _ ↦ he _)
@[to_additive] lemma extend_le_one (hg : g ≤ 1) (he : e ≤ 1) : extend f g e ≤ 1 :=
  fun _b ↦ by classical exact dite_le_one (fun _ ↦ hg _) (fun _ ↦ he _)
end extend
end Function
namespace Pi
variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}
@[to_additive (attr := simp)]
lemma mulSingle_le_mulSingle : mulSingle i a ≤ mulSingle i b ↔ a ≤ b := by
  simp [mulSingle, update_le_update_iff]
@[to_additive (attr := gcongr)] alias ⟨_, GCongr.mulSingle_mono⟩ := mulSingle_le_mulSingle
@[to_additive (attr := simp) single_nonneg]
lemma one_le_mulSingle : 1 ≤ mulSingle i a ↔ 1 ≤ a := by simp [mulSingle]
@[to_additive (attr := simp)]
lemma mulSingle_le_one : mulSingle i a ≤ 1 ↔ a ≤ 1 := by simp [mulSingle]
end Pi