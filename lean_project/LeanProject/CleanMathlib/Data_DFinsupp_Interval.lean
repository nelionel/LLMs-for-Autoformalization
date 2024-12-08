import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Order
import Mathlib.Order.Interval.Finset.Basic
open DFinsupp Finset
open Pointwise
variable {ι : Type*} {α : ι → Type*}
namespace Finset
variable [DecidableEq ι] [∀ i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : ∀ i, Finset (α i)}
def dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert congr_fun h ⟨i, hi⟩⟩
@[simp]
theorem card_dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : #(s.dfinsupp t) = ∏ i ∈ s, #(t i) :=
  (card_map _).trans <| card_pi _ _
variable [∀ i, DecidableEq (α i)]
theorem mem_dfinsupp_iff : f ∈ s.dfinsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Function.Embedding.coeFn_mk] 
    refine ⟨support_mk_subset, fun i hi => ?_⟩
    convert mem_pi.1 hf i hi
    exact mk_of_mem hi
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    dsimp
    exact ite_eq_left_iff.2 fun hi => (not_mem_support_iff.1 fun H => hi <| h.1 H).symm
@[simp]
theorem mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.support ⊆ s) :
    f ∈ s.dfinsupp t ↔ ∀ i, f i ∈ t i := by
  refine mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => ?_,
        fun h => ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    · exact h.2 hi
    · rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (not_mem_mono ht hi)]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h
end Finset
open Finset
namespace DFinsupp
section BundledSingleton
variable [∀ i, Zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}
def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩
theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton
end BundledSingleton
section BundledIcc
variable [∀ i, Zero (α i)] [∀ i, PartialOrder (α i)] [∀ i, LocallyFiniteOrder (α i)]
  {f g : Π₀ i, α i} {i : ι} {a : α i}
def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.not_mem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        have hg : g i = 0 := (gs.prop i).resolve_left
            (Multiset.not_mem_mono (Multiset.Le.subset <| Multiset.le_add_left _ _) h)
        simp_rw [hf, hg]
        exact Icc_self _⟩
@[simp]
theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc
theorem support_rangeIcc_subset [DecidableEq ι] [∀ i, DecidableEq (α i)] :
    (f.rangeIcc g).support ⊆ f.support ∪ g.support := by
  refine fun x hx => ?_
  by_contra h
  refine not_mem_support_iff.2 ?_ hx
  rw [rangeIcc_apply, not_mem_support_iff.1 (not_mem_mono subset_union_left h),
    not_mem_support_iff.1 (not_mem_mono subset_union_right h)]
  exact Icc_self _
end BundledIcc
section Pi
variable [∀ i, Zero (α i)] [DecidableEq ι] [∀ i, DecidableEq (α i)]
def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) := f.support.dfinsupp f
@[simp]
theorem mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_dfinsupp_iff_of_support_subset <| Subset.refl _
@[simp]
theorem card_pi (f : Π₀ i, Finset (α i)) : #f.pi = f.prod fun i ↦ #(f i) := by
  rw [pi, card_dfinsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]
end Pi
section PartialOrder
variable [DecidableEq ι] [∀ i, DecidableEq (α i)]
variable [∀ i, PartialOrder (α i)] [∀ i, Zero (α i)] [∀ i, LocallyFiniteOrder (α i)]
instance instLocallyFiniteOrder : LocallyFiniteOrder (Π₀ i, α i) :=
  LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support ∪ g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans ?_
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      rfl)
variable (f g : Π₀ i, α i)
theorem Icc_eq : Icc f g = (f.support ∪ g.support).dfinsupp (f.rangeIcc g) := rfl
lemma card_Icc : #(Icc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) :=
  card_dfinsupp _ _
lemma card_Ico : #(Ico f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
lemma card_Ioc : #(Ioc f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
lemma card_Ioo : #(Ioo f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
end PartialOrder
section Lattice
variable [DecidableEq ι] [∀ i, DecidableEq (α i)] [∀ i, Lattice (α i)] [∀ i, Zero (α i)]
  [∀ i, LocallyFiniteOrder (α i)] (f g : Π₀ i, α i)
lemma card_uIcc : #(uIcc f g) = ∏ i ∈ f.support ∪ g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _
end Lattice
section CanonicallyOrdered
variable [DecidableEq ι] [∀ i, DecidableEq (α i)]
variable [∀ i, CanonicallyOrderedAddCommMonoid (α i)] [∀ i, LocallyFiniteOrder (α i)]
variable (f : Π₀ i, α i)
lemma card_Iic : #(Iic f) = ∏ i ∈ f.support, #(Iic (f i)) := by
  simp_rw [Iic_eq_Icc, card_Icc, DFinsupp.bot_eq_zero, support_zero, empty_union, zero_apply,
    bot_eq_zero]
lemma card_Iio : #(Iio f) = (∏ i ∈ f.support, #(Iic (f i))) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
end CanonicallyOrdered
end DFinsupp