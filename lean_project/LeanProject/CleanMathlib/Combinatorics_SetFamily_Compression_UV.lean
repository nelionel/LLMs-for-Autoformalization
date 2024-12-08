import Mathlib.Combinatorics.SetFamily.Shadow
open Finset
variable {α : Type*}
theorem sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α) :
    { x | Disjoint u x ∧ v ≤ x }.InjOn fun x => (x ⊔ u) \ v := by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v := by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h
namespace UV
section GeneralizedBooleanAlgebra
variable [GeneralizedBooleanAlgebra α] [DecidableRel (@Disjoint α _ _)]
  [DecidableRel ((· ≤ ·) : α → α → Prop)] {s : Finset α} {u v a : α}
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a
theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v ≤ a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩
theorem compress_of_disjoint_of_le' (hva : Disjoint v a) (hua : u ≤ a) :
    compress u v ((a ⊔ v) \ u) = a := by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v ≤ a ⊔ v), hva.mono_right hua⟩),
    sdiff_sup_cancel (le_sup_of_le_left hua), hva.symm.sup_sdiff_cancel_right]
@[simp]
theorem compress_self (u a : α) : compress u u a = a := by
  unfold compress
  split_ifs with h
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl
@[simp]
theorem compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a := by
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans ?_
  rw [sup_sdiff_self_right, sup_sdiff, disjoint_sdiff_self_right.sdiff_eq_left, sup_eq_right]
  exact sdiff_sdiff_le
@[simp]
theorem compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a := by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_iff.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl
variable [DecidableEq α]
def compression (u v : α) (s : Finset α) :=
  {a ∈ s | compress u v a ∈ s} ∪ {a ∈ s.image <| compress u v | a ∉ s}
@[inherit_doc]
scoped[FinsetFamily] notation "𝓒 " => UV.compression
open scoped FinsetFamily
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s
theorem compress_injOn : Set.InjOn (compress u v) ↑{a ∈ s | compress u v a ∉ s} := by
  intro a ha b hb hab
  rw [mem_coe, mem_filter] at ha hb
  rw [compress] at ha hab
  split_ifs at ha hab with has
  · rw [compress] at hb hab
    split_ifs at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim
theorem mem_compression :
    a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm]
protected theorem IsCompressed.eq (h : IsCompressed u v s) : 𝓒 u v s = s := h
@[simp]
theorem compression_self (u : α) (s : Finset α) : 𝓒 u u s = s := by
  unfold compression
  convert union_empty s
  · ext a
    rw [mem_filter, compress_self, and_self_iff]
  · refine eq_empty_of_forall_not_mem fun a ha ↦ ?_
    simp_rw [mem_filter, mem_image, compress_self] at ha
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := ha
    exact hb' hb
theorem isCompressed_self (u : α) (s : Finset α) : IsCompressed u u s := compression_self u s
theorem compress_disjoint :
    Disjoint {a ∈ s | compress u v a ∈ s} {a ∈ s.image <| compress u v | a ∉ s} :=
  disjoint_left.2 fun _a ha₁ ha₂ ↦ (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1
theorem compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s := by
  rw [mem_compression]
  by_cases h : compress u v a ∈ s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩
theorem compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) :
    compress u v a ∈ 𝓒 u v s := by
  rw [mem_compression] at ha ⊢
  simp only [compress_idem, exists_prop]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩
@[simp]
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s := by
  have h : {a ∈ 𝓒 u v s | compress u v a ∉ 𝓒 u v s} = ∅ :=
    filter_false_of_mem fun a ha h ↦ h <| compress_mem_compression_of_mem_compression ha
  rw [compression, filter_image, h, image_empty, ← h]
  exact filter_union_filter_neg_eq _ (compression u v s)
@[simp]
theorem card_compression (u v : α) (s : Finset α) : #(𝓒 u v s) = #s := by
  rw [compression, card_union_of_disjoint compress_disjoint, filter_image,
    card_image_of_injOn compress_injOn, ← card_union_of_disjoint (disjoint_filter_filter_neg s _ _),
    filter_union_filter_neg_eq]
theorem le_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : u ≤ a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba
theorem disjoint_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : Disjoint v a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba
theorem sup_sdiff_mem_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) :
    (a ⊔ v) \ u ∈ s := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba
theorem sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : Disjoint u a) :
    (a ⊔ u) \ v ∈ s := by
  rw [mem_compression, compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ := by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine hua.mono_right ?_
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact sdiff_le_sdiff_right le_sup_right
  have hv : v = ⊥ := by
    rw [← disjoint_self]
    apply Disjoint.mono_right hva
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact disjoint_sdiff_self_right
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot]
theorem mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) :
    a ∈ s := by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs at h
  · rw [← h, le_sdiff_iff] at hva
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]
end GeneralizedBooleanAlgebra
open FinsetFamily
variable [DecidableEq α] {𝒜 : Finset (Finset α)} {u v : Finset α} {r : ℕ}
theorem card_compress (huv : #u = #v) (a : Finset α) : #(compress u v a) = #a := by
  unfold compress
  split_ifs with h
  · rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_union_of_disjoint h.1.symm, huv,
      add_tsub_cancel_right]
  · rfl
lemma _root_.Set.Sized.uvCompression (huv : #u = #v) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (𝓒 u v 𝒜 : Set (Finset α)).Sized r := by
  simp_rw [Set.Sized, mem_coe, mem_compression]
  rintro s (hs | ⟨huvt, t, ht, rfl⟩)
  · exact h𝒜 hs.1
  · rw [card_compress huv, h𝒜 ht]
private theorem aux (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    v = ∅ → u = ∅ := by
  rintro rfl; refine eq_empty_of_forall_not_mem fun a ha ↦ ?_; obtain ⟨_, ⟨⟩, -⟩ := huv a ha
theorem shadow_compression_subset_compression_shadow (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    ∂ (𝓒 u v 𝒜) ⊆ 𝓒 u v (∂ 𝒜) := by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H : ∀ s ∈ ∂ 𝒜',
      s ∉ ∂ 𝒜 → u ⊆ s ∧ Disjoint v s ∧ (s ∪ v) \ u ∈ ∂ 𝒜 ∧ (s ∪ v) \ u ∉ ∂ 𝒜' by
    rintro s hs'
    rw [mem_compression]
    by_cases hs : s ∈ 𝒜.shadow
    swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩
    refine Or.inl ⟨hs, ?_⟩
    rw [compress]
    split_ifs with huvs
    swap
    · exact hs
    rw [mem_shadow_iff] at hs'
    obtain ⟨t, Ht, a, hat, rfl⟩ := hs'
    have hav : a ∉ v := not_mem_mono huvs.2 (not_mem_erase a t)
    have hvt : v ≤ t := huvs.2.trans (erase_subset _ t)
    have ht : t ∈ 𝒜 := mem_of_mem_compression Ht hvt (aux huv)
    by_cases hau : a ∈ u
    · obtain ⟨b, hbv, Hcomp⟩ := huv a hau
      refine mem_shadow_iff_insert_mem.2 ⟨b, not_mem_sdiff_of_mem_right hbv, ?_⟩
      rw [← Hcomp.eq] at ht
      have hsb :=
        sup_sdiff_mem_of_mem_compression ht ((erase_subset _ _).trans hvt)
          (disjoint_erase_comm.2 huvs.1)
      rwa [sup_eq_union, sdiff_erase (mem_union_left _ <| hvt hbv), union_erase_of_mem hat, ←
        erase_union_of_mem hau] at hsb
    · refine mem_shadow_iff.2
        ⟨(t ⊔ u) \ v,
          sup_sdiff_mem_of_mem_compression Ht hvt <| disjoint_of_erase_right hau huvs.1, a, ?_, ?_⟩
      · rw [sup_eq_union, mem_sdiff, mem_union]
        exact ⟨Or.inl hat, hav⟩
      · rw [← erase_sdiff_comm, sup_eq_union, erase_union_distrib, erase_eq_of_not_mem hau]
  intro s hs𝒜' hs𝒜
  have m : ∀ y, y ∉ s → insert y s ∉ 𝒜 := fun y h a => hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩)
  obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜'
  have hus : u ⊆ insert x s := le_of_mem_compression_of_not_mem ‹_ ∈ 𝒜'› (m _ ‹x ∉ s›)
  have hvs : Disjoint v (insert x s) := disjoint_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›)
  have : (insert x s ∪ v) \ u ∈ 𝒜 := sup_sdiff_mem_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›)
  have hsv : Disjoint s v := hvs.symm.mono_left (subset_insert _ _)
  have hvu : Disjoint v u := disjoint_of_subset_right hus hvs
  have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _)
  have : v \ u = v := ‹Disjoint v u›.sdiff_eq_left
  have : x ∉ u := by
    intro hxu
    obtain ⟨y, hyv, hxy⟩ := huv x hxu
    apply m y (disjoint_right.1 hsv hyv)
    have : ((insert x s ∪ v) \ u ∪ erase u x) \ erase v y ∈ 𝒜 := by
      refine
        sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ?_
          (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff)
      rw [union_sdiff_distrib, ‹v \ u = v›]
      exact (erase_subset _ _).trans subset_union_right
    convert this using 1
    rw [sdiff_union_erase_cancel (hus.trans subset_union_left) ‹x ∈ u›, erase_union_distrib,
      erase_insert ‹x ∉ s›, erase_eq_of_not_mem ‹x ∉ v›, sdiff_erase (mem_union_right _ hyv),
      union_sdiff_cancel_right hsv]
  have hus : u ⊆ s := by rwa [← erase_eq_of_not_mem ‹x ∉ u›, ← subset_insert_iff]
  simp_rw [mem_shadow_iff_insert_mem]
  refine ⟨hus, hsv.symm, ⟨x, ?_, ?_⟩, ?_⟩
  · exact not_mem_sdiff_of_not_mem_left (not_mem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩)
  · rwa [← insert_sdiff_of_not_mem _ ‹x ∉ u›, ← insert_union]
  rintro ⟨w, hwB, hw𝒜'⟩
  have : v ⊆ insert w ((s ∪ v) \ u) :=
    (subset_sdiff.2 ⟨subset_union_right, hvu⟩).trans (subset_insert _ _)
  by_cases hwu : w ∈ u
  · obtain ⟨z, hz, hxy⟩ := huv w hwu
    apply m z (disjoint_right.1 hsv hz)
    have : insert w ((s ∪ v) \ u) ∈ 𝒜 := mem_of_mem_compression hw𝒜' ‹_› (aux huv)
    have : (insert w ((s ∪ v) \ u) ∪ erase u w) \ erase v z ∈ 𝒜 := by
      refine sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ((erase_subset _ _).trans ‹_›) ?_
      rw [← sdiff_erase (mem_union_left _ <| hus hwu)]
      exact disjoint_sdiff
    convert this using 1
    rw [insert_union_comm, insert_erase ‹w ∈ u›,
      sdiff_union_of_subset (hus.trans subset_union_left),
      sdiff_erase (mem_union_right _ ‹z ∈ v›), union_sdiff_cancel_right hsv]
  rw [mem_sdiff, ← Classical.not_imp, Classical.not_not] at hwB
  apply m w (hwu ∘ hwB ∘ mem_union_left _)
  have : (insert w ((s ∪ v) \ u) ∪ u) \ v ∈ 𝒜 :=
    sup_sdiff_mem_of_mem_compression ‹insert w ((s ∪ v) \ u) ∈ 𝒜'› ‹_›
      (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩)
  convert this using 1
  rw [insert_union, sdiff_union_of_subset (hus.trans subset_union_left),
    insert_sdiff_of_not_mem _ (hwu ∘ hwB ∘ mem_union_right _), union_sdiff_cancel_right hsv]
theorem card_shadow_compression_le (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    #(∂ (𝓒 u v 𝒜)) ≤ #(∂ 𝒜) :=
  (card_le_card <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le
end UV