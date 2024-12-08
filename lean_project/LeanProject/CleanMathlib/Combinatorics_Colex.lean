import Mathlib.Algebra.GeomSum
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Nat.BitIndices
import Mathlib.Order.SupClosed
import Mathlib.Order.UpperLower.Basic
open Finset Function
variable {α β : Type*}
namespace Finset
@[ext]
structure Colex (α) where
  toColex ::
  (ofColex : Finset α)
open Colex
instance : Inhabited (Colex α) := ⟨⟨∅⟩⟩
@[simp] lemma toColex_ofColex (s : Colex α) : toColex (ofColex s) = s := rfl
lemma ofColex_toColex (s : Finset α) : ofColex (toColex s) = s := rfl
lemma toColex_inj {s t : Finset α} : toColex s = toColex t ↔ s = t := by simp
@[simp]
lemma ofColex_inj {s t : Colex α} : ofColex s = ofColex t ↔ s = t := by cases s; cases t; simp
lemma toColex_ne_toColex {s t : Finset α} : toColex s ≠ toColex t ↔ s ≠ t := by simp
lemma ofColex_ne_ofColex {s t : Colex α} : ofColex s ≠ ofColex t ↔ s ≠ t := by simp
lemma toColex_injective : Injective (toColex : Finset α → Colex α) := fun _ _ ↦ toColex_inj.1
lemma ofColex_injective : Injective (ofColex : Colex α → Finset α) := fun _ _ ↦ ofColex_inj.1
namespace Colex
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}
instance instLE : LE (Colex α) where
  le s t := ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b
private lemma trans_aux (hst : toColex s ≤ toColex t) (htu : toColex t ≤ toColex u)
    (has : a ∈ s) (hat : a ∉ t) : ∃ b, b ∈ u ∧ b ∉ s ∧ a ≤ b := by
  classical
  let s' : Finset α := {b ∈ s | b ∉ t ∧ a ≤ b}
  have ⟨b, hb, hbmax⟩ := exists_maximal s' ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c ∈ u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  have ⟨d, hdu, hdt, hcd⟩ := htu hct hcu
  have had : a ≤ d := hb.2.2.trans <| hbc.trans hcd
  refine ⟨d, hdu, fun hds ↦ ?_, had⟩
  exact hbmax d hds hdt had <| hbc.trans_lt <| hcd.lt_of_ne <| ne_of_mem_of_not_mem hct hdt
private lemma antisymm_aux (hst : toColex s ≤ toColex t) (hts : toColex t ≤ toColex s) : s ⊆ t := by
  intro a has
  by_contra! hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁
instance instPartialOrder : PartialOrder (Colex α) where
  le_refl _ _ ha ha' := (ha' ha).elim
  le_antisymm _ _ hst hts := Colex.ext <| (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a ∈ ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b ∈ ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux hst htu hbs hbt
        exact ⟨c, hcu, hcs, hab.trans hbc⟩
      · exact ⟨b, hbu, hbs, hab⟩
    · exact trans_aux hst htu has hat
lemma le_def {s t : Colex α} :
    s ≤ t ↔ ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b :=
  Iff.rfl
lemma toColex_le_toColex :
    toColex s ≤ toColex t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := Iff.rfl
lemma toColex_lt_toColex :
    toColex s < toColex t ↔ s ≠ t ∧ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]
lemma toColex_mono : Monotone (toColex : Finset α → Colex α) :=
  fun _s _t hst _a has hat ↦ (hat <| hst has).elim
lemma toColex_strictMono : StrictMono (toColex : Finset α → Colex α) :=
  toColex_mono.strictMono_of_injective toColex_injective
lemma toColex_le_toColex_of_subset (h : s ⊆ t) : toColex s ≤ toColex t := toColex_mono h
lemma toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t := toColex_strictMono h
instance instOrderBot : OrderBot (Colex α) where
  bot := toColex ∅
  bot_le s a ha := by cases ha
@[simp] lemma toColex_empty : toColex (∅ : Finset α) = ⊥ := rfl
@[simp] lemma ofColex_bot : ofColex (⊥ : Colex α) = ∅ := rfl
lemma forall_le_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b ≤ a) : ∀ b ∈ s, b ≤ a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans <| ht _ hct
lemma forall_lt_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b < a) : ∀ b ∈ s, b < a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans_lt <| ht _ hct
lemma toColex_le_singleton : toColex s ≤ toColex {a} ↔ ∀ b ∈ s, b ≤ a ∧ (a ∈ s → b = a) := by
  simp only [toColex_le_toColex, mem_singleton, and_assoc, exists_eq_left]
  refine forall₂_congr fun b _ ↦ ?_; obtain rfl | hba := eq_or_ne b a <;> aesop
lemma toColex_lt_singleton : toColex s < toColex {a} ↔ ∀ b ∈ s, b < a := by
  rw [lt_iff_le_and_ne, toColex_le_singleton, toColex_ne_toColex]
  refine ⟨fun h b hb ↦ (h.1 _ hb).1.lt_of_ne ?_,
    fun h ↦ ⟨fun b hb ↦ ⟨(h _ hb).le, fun ha ↦ (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
  · refine h.2 <| eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc ↦ (h.1 _ hc).2 hb⟩
  · simp at h
lemma singleton_le_toColex : (toColex {a} : Colex α) ≤ toColex s ↔ ∃ x ∈ s, a ≤ x := by
  simp [toColex_le_toColex]; by_cases a ∈ s <;> aesop
lemma singleton_le_singleton : (toColex {a} : Colex α) ≤ toColex {b} ↔ a ≤ b := by
  simp [toColex_le_singleton, eq_comm]
lemma singleton_lt_singleton : (toColex {a} : Colex α) < toColex {b} ↔ a < b := by
  simp [toColex_lt_singleton]
lemma le_iff_sdiff_subset_lowerClosure {s t : Colex α} :
    s ≤ t ↔ (ofColex s : Set α) \ ofColex t ⊆ lowerClosure (ofColex t \ ofColex s : Set α) := by
  simp [le_def, Set.subset_def, and_assoc]
section DecidableEq
variable [DecidableEq α]
instance instDecidableEq : DecidableEq (Colex α) := fun s t ↦
  decidable_of_iff' (s.ofColex = t.ofColex) Colex.ext_iff
instance instDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel (Colex α) (· ≤ ·) := fun s t ↦
  decidable_of_iff'
    (∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b) Iff.rfl
instance instDecidableLT [@DecidableRel α (· ≤ ·)] : @DecidableRel (Colex α) (· < ·) :=
  decidableLTOfDecidableLE
lemma toColex_sdiff_le_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) ≤ toColex (t \ u) ↔ toColex s ≤ toColex t := by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right (show u ≤ s from hus),
    sdiff_sdiff_sdiff_cancel_right (show u ≤ t from hut)]
lemma toColex_sdiff_lt_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus) <|
    toColex_sdiff_le_toColex_sdiff hus hut
@[simp] lemma toColex_sdiff_le_toColex_sdiff' :
    toColex (s \ t) ≤ toColex (t \ s) ↔ toColex s ≤ toColex t := by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right
@[simp] lemma toColex_sdiff_lt_toColex_sdiff' :
 toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t := by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right
end DecidableEq
@[simp] lemma cons_le_cons (ha hb) : toColex (s.cons a ha) ≤ toColex (s.cons b hb) ↔ a ≤ b := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff', cons_sdiff_cons hab, cons_sdiff_cons hab.symm,
    singleton_le_singleton]
@[simp] lemma cons_lt_cons (ha hb) : toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)
variable [DecidableEq α]
lemma insert_le_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) ≤ toColex (insert b s) ↔ a ≤ b := by
  rw [← cons_eq_insert _ _ ha, ← cons_eq_insert _ _ hb, cons_le_cons]
lemma insert_lt_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) < toColex (insert b s) ↔ a < b := by
  rw [← cons_eq_insert _ _ ha, ← cons_eq_insert _ _ hb, cons_lt_cons]
lemma erase_le_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) ≤ toColex (s.erase b) ↔ b ≤ a := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff', erase_sdiff_erase hab hb, erase_sdiff_erase hab.symm ha,
    singleton_le_singleton]
lemma erase_lt_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) < toColex (s.erase b) ↔ b < a :=
  lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)
end PartialOrder
variable [LinearOrder α] [LinearOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α} {r : ℕ}
instance instLinearOrder : LinearOrder (Colex α) where
  le_total s t := by
    classical
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id (symmDiff_nonempty.2 <| ofColex_ne_ofColex.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha b hbt hbs ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inl ⟨hbt, hbs⟩⟩)
  decidableLE := instDecidableLE
  decidableLT := instDecidableLT
open scoped symmDiff
private lemma max_mem_aux {s t : Colex α} (hst : s ≠ t) : (ofColex s ∆ ofColex t).Nonempty := by
  simpa
lemma toColex_lt_toColex_iff_exists_forall_lt :
    toColex s < toColex t ↔ ∃ a ∈ t, a ∉ s ∧ ∀ b ∈ s, b ∉ t → b < a := by
  rw [← not_le, toColex_le_toColex, not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop, exists_and_left]
lemma lt_iff_exists_forall_lt {s t : Colex α} :
    s < t ↔ ∃ a ∈ ofColex t, a ∉ ofColex s ∧ ∀ b ∈ ofColex s, b ∉ ofColex t → b < a :=
  toColex_lt_toColex_iff_exists_forall_lt
lemma toColex_le_toColex_iff_max'_mem :
    toColex s ≤ toColex t ↔ ∀ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  refine ⟨fun h hst ↦ ?_, fun h a has hat ↦ ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m ∈ s := by simpa [mem_symmDiff, hmt] using max'_mem _ <| symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
    exact lt_irrefl _ <| (max'_lt_iff _ _).1 (hmb.lt_of_ne <| ne_of_mem_of_not_mem hms hbs) _ <|
      mem_symmDiff.2 <| Or.inr ⟨hbt, hbs⟩
  · have hst : s ≠ t := ne_of_mem_of_not_mem' has hat
    refine ⟨_, h hst, ?_, le_max' _ _ <| mem_symmDiff.2 <| Or.inl ⟨has, hat⟩⟩
    simpa [mem_symmDiff, h hst] using max'_mem _ <| symmDiff_nonempty.2 hst
lemma le_iff_max'_mem {s t : Colex α} :
    s ≤ t ↔ ∀ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t :=
  toColex_le_toColex_iff_max'_mem.trans
    ⟨fun h hst ↦ h <| ofColex_ne_ofColex.2 hst, fun h hst ↦ h <| ofColex_ne_ofColex.1 hst⟩
lemma toColex_lt_toColex_iff_max'_mem :
    toColex s < toColex t ↔ ∃ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  rw [lt_iff_le_and_ne, toColex_le_toColex_iff_max'_mem]; aesop
lemma lt_iff_max'_mem {s t : Colex α} :
    s < t ↔ ∃ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t := by
  rw [lt_iff_le_and_ne, le_iff_max'_mem]; aesop
lemma lt_iff_exists_filter_lt :
    toColex s < toColex t ↔ ∃ w ∈ t \ s, {a ∈ s | w < a} = {a ∈ t | w < a} := by
  simp only [lt_iff_exists_forall_lt, mem_sdiff, filter_inj, and_assoc]
  refine ⟨fun h ↦ ?_, ?_⟩
  · let u := {w ∈ t \ s | ∀ a ∈ s, a ∉ t → a < w}
    have mem_u {w : α} : w ∈ u ↔ w ∈ t ∧ w ∉ s ∧ ∀ a ∈ s, a ∉ t → a < w := by simp [u, and_assoc]
    have hu : u.Nonempty := h.imp fun _ ↦ mem_u.2
    let m := max' _ hu
    have ⟨hmt, hms, hm⟩ : m ∈ t ∧ m ∉ s ∧ ∀ a ∈ s, a ∉ t → a < m := mem_u.1 <| max'_mem _ _
    refine ⟨m, hmt, hms, fun a hma ↦ ⟨fun has ↦ not_imp_comm.1 (hm _ has) hma.asymm, fun hat ↦ ?_⟩⟩
    by_contra has
    have hau : a ∈ u := mem_u.2 ⟨hat, has, fun b hbs hbt ↦ (hm _ hbs hbt).trans hma⟩
    exact hma.not_le <| le_max' _ _ hau
  · rintro ⟨w, hwt, hws, hw⟩
    refine ⟨w, hwt, hws, fun a has hat ↦ ?_⟩
    by_contra! hwa
    exact hat <| (hw <| hwa.lt_of_ne <| ne_of_mem_of_not_mem hwt hat).1 has
lemma erase_le_erase_min' (hst : toColex s ≤ toColex t) (hcard : #s ≤ #t) (ha : a ∈ s) :
    toColex (s.erase a) ≤
      toColex (t.erase <| min' t <| card_pos.1 <| (card_pos.2 ⟨a, ha⟩).trans_le hcard) := by
  generalize_proofs ht
  set m := min' t ht
  obtain rfl | h' := eq_or_ne s t
  · exact (erase_le_erase ha <| min'_mem _ _).2 <| min'_le _ _ <| ha
  replace hst := hst.lt_of_ne <| toColex_inj.not.2 h'
  simp only [lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc] at hst
  obtain ⟨w, hwt, hws, hw⟩ := hst
  obtain hwa | haw := (ne_of_mem_of_not_mem ha hws).symm.lt_or_lt
  · have hma : m < a := (min'_le _ _ hwt).trans_lt hwa
    refine (lt_iff_exists_forall_lt.2 ⟨a, mem_erase.2 ⟨hma.ne', (hw hwa).1 ha⟩,
      not_mem_erase _ _, fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hab
      exact hbt <| (hw <| hwa.trans_le hab).1 <| mem_of_mem_erase hbs
  obtain rfl | hmw : m = w ∨ m < w := (min'_le _ _ hwt).eq_or_lt
  · have : erase t m ⊆ erase s a := by
      rintro b hb
      rw [mem_erase] at hb ⊢
      exact ⟨(haw.trans_le <| min'_le _ _ hb.2).ne',
        (hw <| hb.1.lt_of_le' <| min'_le _ _ hb.2).2 hb.2⟩
    rw [eq_of_subset_of_card_le this]
    rw [card_erase_of_mem ha, card_erase_of_mem (min'_mem _ _)]
    exact tsub_le_tsub_right hcard _
  · refine (lt_iff_exists_forall_lt.2 ⟨w, mem_erase.2 ⟨hmw.ne', hwt⟩, mt mem_of_mem_erase hws,
      fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hwb
      exact hbt <| (hw <| hwb.lt_of_ne <| ne_of_mem_of_not_mem hwt hbt).1 <| mem_of_mem_erase hbs
lemma toColex_image_le_toColex_image (hf : StrictMono f) :
    toColex (s.image f) ≤ toColex (t.image f) ↔ toColex s ≤ toColex t := by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]
lemma toColex_image_lt_toColex_image (hf : StrictMono f) :
    toColex (s.image f) < toColex (t.image f) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le <| toColex_image_le_toColex_image hf
lemma toColex_image_ofColex_strictMono (hf : StrictMono f) :
    StrictMono fun s ↦ toColex <| image f <| ofColex s :=
  fun _s _t ↦ (toColex_image_lt_toColex_image hf).2
section Fintype
variable [Fintype α]
instance instBoundedOrder : BoundedOrder (Colex α) where
  top := toColex univ
  le_top _x := toColex_le_toColex_of_subset <| subset_univ _
@[simp] lemma toColex_univ : toColex (univ : Finset α) = ⊤ := rfl
@[simp] lemma ofColex_top : ofColex (⊤ : Colex α) = univ := rfl
end Fintype
def IsInitSeg (𝒜 : Finset (Finset α)) (r : ℕ) : Prop :=
  (𝒜 : Set (Finset α)).Sized r ∧
    ∀ ⦃s t : Finset α⦄, s ∈ 𝒜 → toColex t < toColex s ∧ #t = r → t ∈ 𝒜
@[simp] lemma isInitSeg_empty : IsInitSeg (∅ : Finset (Finset α)) r := by simp [IsInitSeg]
lemma IsInitSeg.total (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ := by
  classical
  simp_rw [← sdiff_eq_empty_iff_subset, ← not_nonempty_iff_eq_empty]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex α) (· < ·) (toColex s) (toColex t)
  · exact hs.2 <| h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex.injEq] at hst
    exact ht.2 <| hst ▸ hs.1
  · exact ht.2 <| h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩
variable [Fintype α]
def initSeg (s : Finset α) : Finset (Finset α) := {t | #s = #t ∧ toColex t ≤ toColex s}
@[simp]
lemma mem_initSeg : t ∈ initSeg s ↔ #s = #t ∧ toColex t ≤ toColex s := by simp [initSeg]
lemma mem_initSeg_self : s ∈ initSeg s := by simp
@[simp] lemma initSeg_nonempty : (initSeg s).Nonempty := ⟨s, mem_initSeg_self⟩
lemma isInitSeg_initSeg : IsInitSeg (initSeg s) #s := by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ ↦ mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2
lemma IsInitSeg.exists_initSeg (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    ∃ s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha ↦ by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p ↦ ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toColex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ ∃ s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  refine ⟨fun h𝒜 ↦ h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩
end Colex
open Colex
section Nat
variable {s t : Finset ℕ} {n : ℕ}
lemma geomSum_ofColex_strictMono (hn : 2 ≤ n) : StrictMono fun s ↦ ∑ k ∈ ofColex s, n ^ k := by
  rintro ⟨s⟩ ⟨t⟩ hst
  rw [toColex_lt_toColex_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
  exact (Nat.geomSum_lt hn <| by simpa).trans_le <| single_le_sum (fun _ _ ↦ by positivity) <|
    mem_sdiff.2 ⟨hat, has⟩
lemma geomSum_le_geomSum_iff_toColex_le_toColex (hn : 2 ≤ n) :
    ∑ k ∈ s, n ^ k ≤ ∑ k ∈ t, n ^ k ↔ toColex s ≤ toColex t :=
  (geomSum_ofColex_strictMono hn).le_iff_le
lemma geomSum_lt_geomSum_iff_toColex_lt_toColex (hn : 2 ≤ n) :
    ∑ i ∈ s, n ^ i < ∑ i ∈ t, n ^ i ↔ toColex s < toColex t :=
  (geomSum_ofColex_strictMono hn).lt_iff_lt
theorem geomSum_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (fun s : Finset ℕ ↦ ∑ i in s, n ^ i) := by
  intro _ _ h
  rwa [le_antisymm_iff, geomSum_le_geomSum_iff_toColex_le_toColex hn,
    geomSum_le_geomSum_iff_toColex_le_toColex hn, ← le_antisymm_iff, Colex.toColex.injEq] at h
theorem lt_geomSum_of_mem {a : ℕ} (hn : 2 ≤ n) (hi : a ∈ s) : a < ∑ i in s, n ^ i :=
  (a.lt_pow_self hn).trans_le <| single_le_sum (by simp) hi
@[simp] theorem toFinset_bitIndices_twoPowSum (s : Finset ℕ) :
    (∑ i in s, 2 ^ i).bitIndices.toFinset = s := by
  simp [← (geomSum_injective rfl.le).eq_iff, List.sum_toFinset _ Nat.bitIndices_sorted.nodup]
@[simp] theorem twoPowSum_toFinset_bitIndices (n : ℕ) :
    ∑ i in n.bitIndices.toFinset, 2 ^ i = n := by
  simp [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]
@[simps] def equivBitIndices : ℕ ≃ Finset ℕ where
  toFun n := n.bitIndices.toFinset
  invFun s := ∑ i in s, 2^i
  left_inv := twoPowSum_toFinset_bitIndices
  right_inv := toFinset_bitIndices_twoPowSum
@[simps] def orderIsoColex : ℕ ≃o Colex ℕ where
  toFun n := Colex.toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm s.ofColex
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s :=  Finset.toColex_inj.2 (equivBitIndices.apply_symm_apply s.ofColex)
  map_rel_iff' := by simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le),
    toFinset_bitIndices_twoPowSum]
end Nat
end Finset