import Mathlib.Logic.Basic
import Mathlib.Tactic.Positivity.Basic
library_note "out-param inheritance"
open Function
variable {ι F α β γ δ : Type*}
class NonnegHomClass (F : Type*) (α β : outParam Type*) [Zero β] [LE β] [FunLike F α β] : Prop where
  apply_nonneg (f : F) : ∀ a, 0 ≤ f a
class SubadditiveHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [Add β] [LE β] [FunLike F α β] : Prop where
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
@[to_additive SubadditiveHomClass]
class SubmultiplicativeHomClass (F : Type*) (α β : outParam (Type*)) [Mul α] [Mul β] [LE β]
    [FunLike F α β] : Prop where
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b
@[to_additive SubadditiveHomClass]
class MulLEAddHomClass (F : Type*) (α β : outParam Type*) [Mul α] [Add β] [LE β] [FunLike F α β] :
    Prop where
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b
class NonarchimedeanHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [LinearOrder β] [FunLike F α β] : Prop where
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)
export NonnegHomClass (apply_nonneg)
export SubadditiveHomClass (map_add_le_add)
export SubmultiplicativeHomClass (map_mul_le_mul)
export MulLEAddHomClass (map_mul_le_add)
export NonarchimedeanHomClass (map_add_le_max)
attribute [simp] apply_nonneg
variable [FunLike F α β]
@[to_additive]
theorem le_map_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel] using map_mul_le_mul f (a / b) b
@[to_additive existing]
theorem le_map_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel] using map_mul_le_add f (a / b) b
@[to_additive]
theorem le_map_div_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel] using map_mul_le_mul f (a / b) (b / c)
@[to_additive existing]
theorem le_map_div_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel] using map_mul_le_add f (a / b) (b / c)
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function
@[positivity DFunLike.coe _ _]
def evalMap : PositivityExt where eval {_ β} _ _ e := do
  let .app (.app _ f) a ← whnfR e
    | throwError "not ↑f · where f is of NonnegHomClass"
  let pa ← mkAppOptM ``apply_nonneg #[none, none, β, none, none, none, none, f, a]
  pure (.nonnegative pa)
end Mathlib.Meta.Positivity
class AddGroupSeminormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [OrderedAddCommMonoid β] [FunLike F α β]
  extends SubadditiveHomClass F α β : Prop where
  map_zero (f : F) : f 0 = 0
  map_neg_eq_map (f : F) (a : α) : f (-a) = f a
@[to_additive]
class GroupSeminormClass (F : Type*) (α β : outParam Type*)
    [Group α] [OrderedAddCommMonoid β] [FunLike F α β]
  extends MulLEAddHomClass F α β : Prop where
  map_one_eq_zero (f : F) : f 1 = 0
  map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a
class AddGroupNormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [OrderedAddCommMonoid β] [FunLike F α β]
  extends AddGroupSeminormClass F α β : Prop where
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0
@[to_additive]
class GroupNormClass (F : Type*) (α β : outParam Type*)
    [Group α] [OrderedAddCommMonoid β] [FunLike F α β]
  extends GroupSeminormClass F α β : Prop where
  eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1
export AddGroupSeminormClass (map_neg_eq_map)
export GroupSeminormClass (map_one_eq_zero map_inv_eq_map)
export AddGroupNormClass (eq_zero_of_map_eq_zero)
export GroupNormClass (eq_one_of_map_eq_zero)
attribute [simp] map_one_eq_zero 
attribute [simp] map_neg_eq_map
attribute [simp] map_inv_eq_map 
attribute [to_additive] GroupSeminormClass.toMulLEAddHomClass
instance (priority := 100) AddGroupSeminormClass.toZeroHomClass [AddGroup α]
    [OrderedAddCommMonoid β] [AddGroupSeminormClass F α β] : ZeroHomClass F α β :=
  { ‹AddGroupSeminormClass F α β› with }
section GroupSeminormClass
variable [Group α] [OrderedAddCommMonoid β] [GroupSeminormClass F α β] (f : F) (x y : α)
@[to_additive]
theorem map_div_le_add : f (x / y) ≤ f x + f y := by
  rw [div_eq_mul_inv, ← map_inv_eq_map f y]
  exact map_mul_le_add _ _ _
@[to_additive]
theorem map_div_rev : f (x / y) = f (y / x) := by rw [← inv_div, map_inv_eq_map]
@[to_additive]
theorem le_map_add_map_div' : f x ≤ f y + f (y / x) := by
  simpa only [add_comm, map_div_rev, div_mul_cancel] using map_mul_le_add f (x / y) y
end GroupSeminormClass
example [OrderedAddCommGroup β] : OrderedAddCommMonoid β :=
  inferInstance
@[to_additive]
theorem abs_sub_map_le_div [Group α] [LinearOrderedAddCommGroup β] [GroupSeminormClass F α β]
    (f : F) (x y : α) : |f x - f y| ≤ f (x / y) := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩
@[to_additive]
instance (priority := 100) GroupSeminormClass.toNonnegHomClass [Group α]
    [LinearOrderedAddCommMonoid β] [GroupSeminormClass F α β] : NonnegHomClass F α β :=
  { ‹GroupSeminormClass F α β› with
    apply_nonneg := fun f a =>
      (nsmul_nonneg_iff two_ne_zero).1 <| by
        rw [two_nsmul, ← map_one_eq_zero f, ← div_self' a]
        exact map_div_le_add _ _ _ }
section GroupNormClass
variable [Group α] [OrderedAddCommMonoid β] [GroupNormClass F α β] (f : F) {x : α}
@[to_additive (attr := simp)]
theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
  ⟨eq_one_of_map_eq_zero _, by
    rintro rfl
    exact map_one_eq_zero _⟩
@[to_additive]
theorem map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 :=
  (map_eq_zero_iff_eq_one _).not
end GroupNormClass
@[to_additive]
theorem map_pos_of_ne_one [Group α] [LinearOrderedAddCommMonoid β] [GroupNormClass F α β] (f : F)
    {x : α} (hx : x ≠ 1) : 0 < f x :=
  (apply_nonneg _ _).lt_of_ne <| ((map_ne_zero_iff_ne_one _).2 hx).symm
class RingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [OrderedSemiring β] [FunLike F α β]
  extends AddGroupSeminormClass F α β, SubmultiplicativeHomClass F α β : Prop
class RingNormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [OrderedSemiring β] [FunLike F α β]
  extends RingSeminormClass F α β, AddGroupNormClass F α β : Prop
class MulRingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [OrderedSemiring β] [FunLike F α β]
  extends AddGroupSeminormClass F α β, MonoidWithZeroHomClass F α β : Prop
attribute [instance 50]
  MulRingSeminormClass.toMonoidHomClass MulRingSeminormClass.toMonoidWithZeroHomClass
class MulRingNormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [OrderedSemiring β] [FunLike F α β]
  extends MulRingSeminormClass F α β, AddGroupNormClass F α β : Prop
instance (priority := 100) RingSeminormClass.toNonnegHomClass [NonUnitalNonAssocRing α]
    [LinearOrderedSemiring β] [RingSeminormClass F α β] : NonnegHomClass F α β :=
  AddGroupSeminormClass.toNonnegHomClass
instance (priority := 100) MulRingSeminormClass.toRingSeminormClass [NonAssocRing α]
    [OrderedSemiring β] [MulRingSeminormClass F α β] : RingSeminormClass F α β :=
  { ‹MulRingSeminormClass F α β› with map_mul_le_mul := fun _ _ _ => (map_mul _ _ _).le }
instance (priority := 100) MulRingNormClass.toRingNormClass [NonAssocRing α]
    [OrderedSemiring β] [MulRingNormClass F α β] : RingNormClass F α β :=
  { ‹MulRingNormClass F α β›, MulRingSeminormClass.toRingSeminormClass with }