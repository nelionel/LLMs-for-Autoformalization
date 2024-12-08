import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Subgroup.Centralizer
variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]
variable {N : Type*} [Group N]
namespace Subgroup
theorem range_zpowersHom (g : G) : (zpowersHom G g).range = zpowers g := rfl
@[to_additive]
instance (a : G) : Countable (zpowers a) := Set.surjective_onto_range.countable
end Subgroup
namespace AddSubgroup
@[simp]
theorem range_zmultiplesHom (a : A) : (zmultiplesHom A a).range = zmultiples a :=
  rfl
attribute [to_additive existing (attr := simp)] Subgroup.range_zpowersHom
section Ring
variable {R : Type*} [Ring R] (r : R) (k : ℤ)
@[simp]
theorem intCast_mul_mem_zmultiples : ↑(k : ℤ) * r ∈ zmultiples r := by
  simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k
@[deprecated (since := "2024-04-17")]
alias int_cast_mul_mem_zmultiples := intCast_mul_mem_zmultiples
@[simp]
theorem intCast_mem_zmultiples_one : ↑(k : ℤ) ∈ zmultiples (1 : R) :=
  mem_zmultiples_iff.mp ⟨k, by simp⟩
@[deprecated (since := "2024-04-17")]
alias int_cast_mem_zmultiples_one := intCast_mem_zmultiples_one
end Ring
end AddSubgroup
@[simp] lemma Int.range_castAddHom {A : Type*} [AddGroupWithOne A] :
    (Int.castAddHom A).range = AddSubgroup.zmultiples 1 := by
  ext a
  simp_rw [AddMonoidHom.mem_range, Int.coe_castAddHom, AddSubgroup.mem_zmultiples_iff, zsmul_one]
namespace Subgroup
variable {s : Set G} {g : G}
@[to_additive]
theorem centralizer_closure (S : Set G) :
    centralizer (closure S : Set G) = ⨅ g ∈ S, centralizer (zpowers g : Set G) :=
  le_antisymm
      (le_iInf fun _ => le_iInf fun hg => centralizer_le <| zpowers_le.2 <| subset_closure hg) <|
    le_centralizer_iff.1 <|
      (closure_le _).2 fun g =>
        SetLike.mem_coe.2 ∘ zpowers_le.1 ∘ le_centralizer_iff.1 ∘ iInf_le_of_le g ∘ iInf_le _
@[to_additive]
theorem center_eq_iInf (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g ∈ S, centralizer (zpowers g) := by
  rw [← centralizer_univ, ← coe_top, ← hS, centralizer_closure]
@[to_additive]
theorem center_eq_infi' (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g : S, centralizer (zpowers (g : G)) := by
  rw [center_eq_iInf S hS, ← iInf_subtype'']
end Subgroup