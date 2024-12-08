import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Basic
variable {α β : Type*}
namespace Finset
section Decidable
variable [DecidableEq α] (s t : Finset α)
instance instLocallyFiniteOrder : LocallyFiniteOrder (Finset α) where
  finsetIcc s t := t.powerset.filter (s ⊆ ·)
  finsetIco s t := t.ssubsets.filter (s ⊆ ·)
  finsetIoc s t := t.powerset.filter (s ⊂ ·)
  finsetIoo s t := t.ssubsets.filter (s ⊂ ·)
  finset_mem_Icc s t u := by
    rw [mem_filter, mem_powerset]
    exact and_comm
  finset_mem_Ico s t u := by
    rw [mem_filter, mem_ssubsets]
    exact and_comm
  finset_mem_Ioc s t u := by
    rw [mem_filter, mem_powerset]
    exact and_comm
  finset_mem_Ioo s t u := by
    rw [mem_filter, mem_ssubsets]
    exact and_comm
theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filter (s ⊆ ·) :=
  rfl
theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filter (s ⊆ ·) :=
  rfl
theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filter (s ⊂ ·) :=
  rfl
theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filter (s ⊂ ·) :=
  rfl
theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem fun t _ => empty_subset t
theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem fun t _ => empty_subset t
variable {s t}
theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image (s ∪ ·) := by
  ext u
  simp_rw [mem_Icc, mem_image, mem_powerset]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h <| hv.trans sdiff_subset⟩
theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image (s ∪ ·) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  rw [← card_sdiff h, ← card_powerset, Icc_eq_image_powerset h, Finset.card_image_iff]
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v)
  rw [mem_coe, mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left, ←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left, huv]
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]
end Decidable
variable [Preorder β] {s t : Finset α} {f : Finset α → β}
section Cons
lemma monotone_iff_forall_le_cons : Monotone f ↔ ∀ s, ∀ ⦃a⦄ (ha), f s ≤ f (cons a s ha) := by
  classical simp [monotone_iff_forall_covBy, covBy_iff_exists_cons]
lemma antitone_iff_forall_cons_le : Antitone f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) ≤ f s :=
  monotone_iff_forall_le_cons (β := βᵒᵈ)
lemma strictMono_iff_forall_lt_cons : StrictMono f ↔ ∀ s ⦃a⦄ ha, f s < f (cons a s ha) := by
  classical simp [strictMono_iff_forall_covBy, covBy_iff_exists_cons]
lemma strictAnti_iff_forall_cons_lt : StrictAnti f ↔ ∀ s ⦃a⦄ ha, f (cons a s ha) < f s :=
  strictMono_iff_forall_lt_cons (β := βᵒᵈ)
end Cons
section Insert
variable [DecidableEq α]
lemma monotone_iff_forall_le_insert : Monotone f ↔ ∀ s ⦃a⦄, a ∉ s → f s ≤ f (insert a s) := by
  simp [monotone_iff_forall_le_cons]
lemma antitone_iff_forall_insert_le : Antitone f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) ≤ f s :=
  monotone_iff_forall_le_insert (β := βᵒᵈ)
lemma strictMono_iff_forall_lt_insert : StrictMono f ↔ ∀ s ⦃a⦄, a ∉ s → f s < f (insert a s) := by
  simp [strictMono_iff_forall_lt_cons]
lemma strictAnti_iff_forall_lt_insert : StrictAnti f ↔ ∀ s ⦃a⦄, a ∉ s → f (insert a s) < f s :=
  strictMono_iff_forall_lt_insert (β := βᵒᵈ)
end Insert
end Finset