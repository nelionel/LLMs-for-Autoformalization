import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Submonoid
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G]
    extends AddSubmonoidClass S G : Prop where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0
@[to_additive]
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] extends
    SubmonoidClass S G : Prop where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1
export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0
@[to_additive]
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1
@[to_additive]
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h
@[to_additive]
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'
class IsMaxCone {S G : Type*} [AddCommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_neg_mem (a : G) : a ∈ C ∨ -a ∈ C
@[to_additive IsMaxCone]
class IsMaxMulCone {S G : Type*} [CommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_inv_mem (a : G) : a ∈ C ∨ a⁻¹ ∈ C
export IsMaxCone (mem_or_neg_mem)
export IsMaxMulCone (mem_or_inv_mem)
namespace GroupCone
variable {H : Type*} [OrderedCommGroup H] {a : H}
variable (H) in
@[to_additive nonneg
"Construct a cone from the set of non-negative elements of a partially ordered abelian group."]
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm
@[to_additive (attr := simp) nonneg_toAddSubmonoid]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp) mem_nonneg]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast) coe_nonneg]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl
@[to_additive nonneg.isMaxCone]
instance oneLE.isMaxMulCone {H : Type*} [LinearOrderedCommGroup H] : IsMaxMulCone (oneLE H) where
  mem_or_inv_mem := by simpa using le_total 1
end GroupCone
variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)
@[to_additive (attr := reducible)
"Construct a partially ordered abelian group by designating a cone in an abelian group."]
def OrderedCommGroup.mkOfCone [GroupConeClass S G] :
    OrderedCommGroup G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)
  mul_le_mul_left a b nab c := by simpa using nab
@[to_additive (attr := reducible)
"Construct a linearly ordered abelian group by designating a maximal cone in an abelian group."]
def LinearOrderedCommGroup.mkOfCone
    [GroupConeClass S G] [IsMaxMulCone C] (dec : DecidablePred (· ∈ C)) :
    LinearOrderedCommGroup G where
  __ := OrderedCommGroup.mkOfCone C
  le_total a b := by simpa using mem_or_inv_mem (b / a)
  decidableLE _ _ := dec _