import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Order.Interval.Finset.Basic
noncomputable section
open Finset Finsupp Function
open scoped Classical
open Pointwise
variable {ι α : Type*}
namespace Finsupp
section RangeSingleton
variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm
theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton
end RangeSingleton
section RangeIcc
variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}
@[simps toFun]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α where
  toFun i := Icc (f i) (g i)
  support :=
    f.support ∪ g.support
  mem_support_toFun i := by
    rw [mem_union, ← not_iff_not, not_or, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm
lemma coe_rangeIcc (f g : ι →₀ α) : rangeIcc f g i = Icc (f i) (g i) := rfl
@[simp]
theorem rangeIcc_support (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := rfl
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc
end RangeIcc
section PartialOrder
variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)
instance instLocallyFiniteOrder : LocallyFiniteOrder (ι →₀ α) :=
  LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.support ∪ g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans ?_
      simp_rw [mem_rangeIcc_apply_iff]
      exact forall_and
theorem Icc_eq : Icc f g = (f.support ∪ g.support).finsupp (f.rangeIcc g) := rfl
theorem card_Icc : #(Icc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)):= by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]
theorem card_Ico : #(Ico f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
theorem card_Ioc : #(Ioc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
theorem card_Ioo : #(Ioo f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
end PartialOrder
section Lattice
variable [Lattice α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)
theorem card_uIcc :
    #(uIcc f g) = ∏ i ∈ f.support ∪ g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι →₀ α) _
end Lattice
section CanonicallyOrdered
variable [CanonicallyOrderedAddCommMonoid α] [LocallyFiniteOrder α]
variable (f : ι →₀ α)
theorem card_Iic : #(Iic f) = ∏ i ∈ f.support, #(Iic (f i)) := by
  classical simp_rw [Iic_eq_Icc, card_Icc, Finsupp.bot_eq_zero, support_zero, empty_union,
      zero_apply, bot_eq_zero]
theorem card_Iio : #(Iio f) = ∏ i ∈ f.support, #(Iic (f i)) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
end CanonicallyOrdered
end Finsupp