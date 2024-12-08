import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Fin
attribute [-instance] instDecidableEqFin
open Nat
open scoped FinsetFamily
namespace Finset
namespace Colex
variable {α : Type*} [LinearOrder α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}
lemma shadow_initSeg [Fintype α] (hs : s.Nonempty) :
    ∂ (initSeg s) = initSeg (erase s <| min' s hs) := by
  ext t
  simp only [mem_shadow_iff_insert_mem, mem_initSeg, exists_prop]
  constructor
  · rintro ⟨a, ha, hst, hts⟩
    constructor
    · rw [card_erase_of_mem (min'_mem _ _), hst, card_insert_of_not_mem ha, add_tsub_cancel_right]
    · simpa [ha] using erase_le_erase_min' hts hst.ge (mem_insert_self _ _)
  simp_rw [le_iff_eq_or_lt, lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc]
  simp only [toColex_inj, ofColex_toColex, ne_eq, and_imp]
  rintro cards' (rfl | ⟨k, hks, hkt, z⟩)
  · refine ⟨min' s hs, not_mem_erase _ _, ?_⟩
    rw [insert_erase (min'_mem _ _)]
    exact ⟨rfl, Or.inl rfl⟩
  set j := min' tᶜ ⟨k, mem_compl.2 hkt⟩
  have hjk : j ≤ k := min'_le _ _ (mem_compl.2 ‹k ∉ t›)
  have : j ∉ t := mem_compl.1 (min'_mem _ _)
  have hcard : #s = #(insert j t) := by
    rw [card_insert_of_not_mem ‹j ∉ t›, ← ‹_ = #t›, card_erase_add_one (min'_mem _ _)]
  refine ⟨j, ‹_›, hcard, ?_⟩
  obtain hjk | r₁ := hjk.lt_or_eq
  · refine Or.inr ⟨k, mem_of_mem_erase ‹_›, fun hk ↦ hkt <| mem_of_mem_insert_of_ne hk hjk.ne',
      fun x hx ↦ ?_⟩
    simpa only [mem_insert, z hx, (hjk.trans hx).ne', mem_erase, Ne, false_or,
      and_iff_right_iff_imp] using fun _ ↦ ((min'_le _ _ <| mem_of_mem_erase hks).trans_lt hx).ne'
  refine Or.inl (eq_of_subset_of_card_le (fun a ha ↦ ?_) hcard.ge).symm
  rcases lt_trichotomy k a with (lt | rfl | gt)
  · apply mem_insert_of_mem
    rw [z lt]
    refine mem_erase_of_ne_of_mem (lt_of_le_of_lt ?_ lt).ne' ha
    apply min'_le _ _ (mem_of_mem_erase ‹_›)
  · rw [r₁]; apply mem_insert_self
  · apply mem_insert_of_mem
    rw [← r₁] at gt
    by_contra
    apply (min'_le tᶜ _ _).not_lt gt
    rwa [mem_compl]
protected lemma IsInitSeg.shadow [Finite α] (h₁ : IsInitSeg 𝒜 r) : IsInitSeg (∂ 𝒜) (r - 1) := by
  cases nonempty_fintype α
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · have : 𝒜 ⊆ {∅} := fun s hs ↦ by rw [mem_singleton, ← Finset.card_eq_zero]; exact h₁.1 hs
    have := shadow_monotone this
    simp only [subset_empty, le_eq_subset, shadow_singleton_empty] at this
    simp [this]
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty
  · simp
  obtain ⟨s, rfl, rfl⟩ := h₁.exists_initSeg h𝒜
  rw [shadow_initSeg (card_pos.1 hr), ← card_erase_of_mem (min'_mem _ _)]
  exact isInitSeg_initSeg
end Colex
open Finset Colex Nat UV
open scoped FinsetFamily
variable {α : Type*} [LinearOrder α] {s U V : Finset α} {n : ℕ}
namespace UV
lemma toColex_compress_lt_toColex {hU : U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV)
    (hA : compress U V s ≠ s) : toColex (compress U V s) < toColex s := by
  rw [compress, ite_ne_right_iff] at hA
  rw [compress, if_pos hA.1, lt_iff_exists_filter_lt]
  simp_rw [mem_sdiff (s := s), filter_inj, and_assoc]
  refine ⟨_, hA.1.2 <| max'_mem _ hV, not_mem_sdiff_of_mem_right <| max'_mem _ _, fun a ha ↦ ?_⟩
  have : a ∉ V := fun H ↦ ha.not_le (le_max' _ _ H)
  have : a ∉ U := fun H ↦ ha.not_lt ((le_max' _ _ H).trans_lt h)
  simp [‹a ∉ U›, ‹a ∉ V›]
private def UsefulCompression (U V : Finset α) : Prop :=
  Disjoint U V ∧ #U = #V ∧ ∃ (HU : U.Nonempty) (HV : V.Nonempty), max' U HU < max' V HV
private instance UsefulCompression.instDecidableRel : @DecidableRel (Finset α) UsefulCompression :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))
private lemma compression_improved (𝒜 : Finset (Finset α)) (h₁ : UsefulCompression U V)
    (h₂ : ∀ ⦃U₁ V₁⦄, UsefulCompression U₁ V₁ → #U₁ < #U → IsCompressed U₁ V₁ 𝒜) :
    #(∂ (𝓒 U V 𝒜)) ≤ #(∂ 𝒜) := by
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁
  refine card_shadow_compression_le _ _ fun x Hx ↦ ⟨min' V hV, min'_mem _ _, ?_⟩
  obtain hU' | hU' := eq_or_lt_of_le (succ_le_iff.2 hU.card_pos)
  · rw [← hU'] at same_size
    have : erase U x = ∅ := by rw [← Finset.card_eq_zero, card_erase_of_mem Hx, ← hU']
    have : erase V (min' V hV) = ∅ := by
      rw [← Finset.card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size]
    rw [‹erase U x = ∅›, ‹erase V (min' V hV) = ∅›]
    exact isCompressed_self _ _
  refine h₂ ⟨UVd.mono (erase_subset ..) (erase_subset ..), ?_, ?_, ?_, ?_⟩ (card_erase_lt_of_mem Hx)
  · rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size]
  · rwa [← card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt]
  · rwa [← Finset.card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, tsub_pos_iff_lt]
  · exact (Finset.max'_subset _ <| erase_subset _ _).trans_lt (max_lt.trans_le <| le_max' _ _ <|
      mem_erase.2 ⟨(min'_lt_max'_of_card _ (by rwa [← same_size])).ne', max'_mem _ _⟩)
lemma isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : ℕ} (h₁ : (ℬ : Set (Finset α)).Sized r)
    (h₂ : ∀ U V, UsefulCompression U V → IsCompressed U V ℬ) : IsInitSeg ℬ r := by
  refine ⟨h₁, ?_⟩
  rintro A B hA ⟨hBA, sizeA⟩
  by_contra hB
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB
  have hAB' : #A = #B := (h₁ hA).trans sizeA.symm
  have hU : (A \ B).Nonempty := sdiff_nonempty.2 fun h ↦ hAB <| eq_of_subset_of_card_le h hAB'.ge
  have hV : (B \ A).Nonempty :=
    sdiff_nonempty.2 fun h ↦ hAB.symm <| eq_of_subset_of_card_le h hAB'.le
  have disj : Disjoint (B \ A) (A \ B) := disjoint_sdiff.mono_left sdiff_subset
  have smaller : max' _ hV < max' _ hU := by
    obtain hlt | heq | hgt := lt_trichotomy (max' _ hU) (max' _ hV)
    · rw [← compress_sdiff_sdiff A B] at hAB hBA
      cases hBA.not_lt <| toColex_compress_lt_toColex hlt hAB
    · exact (disjoint_right.1 disj (max'_mem _ hU) <| heq.symm ▸ max'_mem _ _).elim
    · assumption
  refine hB ?_
  rw [← (h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq]
  exact mem_compression.2 (Or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩)
attribute [-instance] Fintype.decidableForallFintype
private def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ := ∑ A in 𝒜, ∑ a in A, 2 ^ (a : ℕ)
private lemma familyMeasure_compression_lt_familyMeasure {U V : Finset (Fin n)} {hU : U.Nonempty}
    {hV : V.Nonempty} (h : max' U hU < max' V hV) {𝒜 : Finset (Finset (Fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
    familyMeasure (𝓒 U V 𝒜) < familyMeasure 𝒜 := by
  rw [compression] at a ⊢
  have q : ∀ Q ∈ {A ∈ 𝒜 | compress U V A ∉ 𝒜}, compress U V Q ≠ Q := by
    simp_rw [mem_filter]
    intro Q hQ h
    rw [h] at hQ
    exact hQ.2 hQ.1
  have uA : {A ∈ 𝒜 | compress U V A ∈ 𝒜} ∪ {A ∈ 𝒜 | compress U V A ∉ 𝒜} = 𝒜 :=
    filter_union_filter_neg_eq _ _
  have ne₂ : {A ∈ 𝒜 | compress U V A ∉ 𝒜}.Nonempty := by
    refine nonempty_iff_ne_empty.2 fun z ↦ a ?_
    rw [filter_image, z, image_empty, union_empty]
    rwa [z, union_empty] at uA
  rw [familyMeasure, familyMeasure, sum_union compress_disjoint]
  conv_rhs => rw [← uA]
  rw [sum_union (disjoint_filter_filter_neg _ _ _), add_lt_add_iff_left, filter_image,
    sum_image compress_injOn]
  refine sum_lt_sum_of_nonempty ne₂ fun A hA ↦ ?_
  simp_rw [← sum_image Fin.val_injective.injOn]
  rw [geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    toColex_image_lt_toColex_image Fin.val_strictMono]
  exact toColex_compress_lt_toColex h <| q _ hA
private lemma kruskal_katona_helper {r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h : (𝒜 : Set (Finset (Fin n))).Sized r) :
    ∃ ℬ : Finset (Finset (Fin n)), #(∂ ℬ) ≤ #(∂ 𝒜) ∧ #𝒜 = #ℬ ∧
      (ℬ : Set (Finset (Fin n))).Sized r ∧ ∀ U V, UsefulCompression U V → IsCompressed U V ℬ := by
  classical
  set usable : Finset (Finset (Fin n) × Finset (Fin n)) :=
    {t | UsefulCompression t.1 t.2 ∧ ¬ IsCompressed t.1 t.2 𝒜}
  obtain husable | husable := usable.eq_empty_or_nonempty
  · refine ⟨𝒜, le_rfl, rfl, h, fun U V hUV ↦ ?_⟩
    rw [eq_empty_iff_forall_not_mem] at husable
    by_contra h
    exact husable ⟨U, V⟩ <| mem_filter.2 ⟨mem_univ _, hUV, h⟩
  obtain ⟨⟨U, V⟩, hUV, t⟩ := exists_min_image usable (fun t ↦ #t.1) husable
  rw [mem_filter] at hUV
  have h₂ : ∀ U₁ V₁, UsefulCompression U₁ V₁ → #U₁ < #U → IsCompressed U₁ V₁ 𝒜 := by
    rintro U₁ V₁ huseful hUcard
    by_contra h
    exact hUcard.not_le <| t ⟨U₁, V₁⟩ <| mem_filter.2 ⟨mem_univ _, huseful, h⟩
  have p1 : #(∂ (𝓒 U V 𝒜)) ≤ #(∂ 𝒜) := compression_improved _ hUV.2.1 h₂
  obtain ⟨-, hUV', hu, hv, hmax⟩ := hUV.2.1
  have := familyMeasure_compression_lt_familyMeasure hmax hUV.2.2
  obtain ⟨t, q1, q2, q3, q4⟩ := UV.kruskal_katona_helper (𝓒 U V 𝒜) (h.uvCompression hUV')
  exact ⟨t, q1.trans p1, (card_compression _ _ _).symm.trans q2, q3, q4⟩
termination_by familyMeasure 𝒜
end UV
section KK
variable {r k i : ℕ} {𝒜 𝒞 : Finset <| Finset <| Fin n}
theorem kruskal_katona (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : IsInitSeg 𝒞 r) : #(∂ 𝒞) ≤ #(∂ 𝒜) := by
  obtain ⟨𝒜', h𝒜, h𝒜𝒞⟩ := exists_subset_card_eq h𝒞𝒜
  obtain ⟨ℬ, hℬ𝒜, h𝒜ℬ, hℬr, hℬ⟩ := UV.kruskal_katona_helper 𝒜' (h𝒜r.mono (by gcongr))
  suffices ℬ = 𝒞 by subst 𝒞; exact hℬ𝒜.trans (by gcongr)
  have hcard : #ℬ = #𝒞 := h𝒜ℬ.symm.trans h𝒜𝒞
  obtain h𝒞ℬ | hℬ𝒞 := h𝒞.total (UV.isInitSeg_of_compressed hℬr hℬ)
  · exact (eq_of_subset_of_card_le h𝒞ℬ hcard.le).symm
  · exact eq_of_subset_of_card_le hℬ𝒞 hcard.ge
theorem iterated_kk (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : #𝒞 ≤ #𝒜) (h₃ : IsInitSeg 𝒞 r) :
    #(∂^[k] 𝒞) ≤ #(∂^[k] 𝒜) := by
  induction' k with _k ih generalizing r 𝒜 𝒞
  · simpa
  · refine ih h₁.shadow (kruskal_katona h₁ h₂ h₃) ?_
    convert h₃.shadow
theorem kruskal_katona_lovasz_form (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k
  have : (𝒞 : Set (Finset (Fin n))).Sized r := Set.sized_powersetCard _ _
  calc
    k.choose (r - i)
    _ = #(powersetCard (r - i) range'k) := by rw [card_powersetCard, card_attachFin, card_range]
    _ = #(∂^[i] 𝒞) := by
      congr!
      ext B
      rw [mem_powersetCard, mem_shadow_iterate_iff_exists_sdiff]
      constructor
      · rintro ⟨hBk, hB⟩
        have := exists_subsuperset_card_eq hBk (Nat.le_add_left _ i) <| by
          rwa [hB, card_attachFin, card_range, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left]
        obtain ⟨C, BsubC, hCrange, hcard⟩ := this
        rw [hB, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left] at hcard
        refine ⟨C, mem_powersetCard.2 ⟨hCrange, hcard⟩, BsubC, ?_⟩
        rw [card_sdiff BsubC, hcard, hB, Nat.sub_sub_self hir]
      · rintro ⟨A, Ah, hBA, card_sdiff_i⟩
        rw [mem_powersetCard] at Ah
        refine ⟨hBA.trans Ah.1, eq_tsub_of_add_eq ?_⟩
        rw [← Ah.2, ← card_sdiff_i, add_comm, card_sdiff_add_card_eq_card hBA]
    _ ≤ #(∂ ^[i] 𝒜) := by
      refine iterated_kk h₁ ?_ ⟨‹_›, ?_⟩
      · rwa [card_powersetCard, card_attachFin, card_range]
      simp_rw [𝒞, mem_powersetCard]
      rintro A B hA ⟨HB₁, HB₂⟩
      refine ⟨fun t ht ↦ ?_, ‹_›⟩
      rw [mem_attachFin, mem_range]
      have : toColex (image Fin.val B) < toColex (image Fin.val A) := by
        rwa [toColex_image_lt_toColex_image Fin.val_strictMono]
      apply Colex.forall_lt_mono this.le _ t (mem_image.2 ⟨t, ht, rfl⟩)
      simp_rw [mem_image]
      rintro _ ⟨a, ha, hab⟩
      simpa [range'k, hab] using hA.1 ha
end KK
theorem erdos_ko_rado {𝒜 : Finset (Finset (Fin n))} {r : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (h₂ : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h₃ : r ≤ n / 2) :
    #𝒜 ≤ (n - 1).choose (r - 1) := by
  cases' Nat.eq_zero_or_pos r with b h1r
  · convert Nat.zero_le _
    rw [Finset.card_eq_zero, eq_empty_iff_forall_not_mem]
    refine fun A HA ↦ h𝒜 HA HA ?_
    rw [disjoint_self_iff_empty, ← Finset.card_eq_zero, ← b]
    exact h₂ HA
  refine le_of_not_lt fun size ↦ ?_
  have : Disjoint 𝒜 (∂^[n - 2 * r] 𝒜ᶜˢ) := disjoint_right.2 fun A hAbar hA ↦ by
    simp [mem_shadow_iterate_iff_exists_sdiff, mem_compls] at hAbar
    obtain ⟨C, hC, hAC, _⟩ := hAbar
    exact h𝒜 hA hC (disjoint_of_subset_left hAC disjoint_compl_right)
  have : r ≤ n := h₃.trans (Nat.div_le_self n 2)
  have : 1 ≤ n := ‹1 ≤ r›.trans ‹r ≤ n›
  have z : (n - 1).choose (n - r) < #𝒜ᶜˢ := by
    rwa [card_compls, choose_symm_of_eq_add (tsub_add_tsub_cancel ‹r ≤ n› ‹1 ≤ r›).symm]
  have h𝒜bar : (𝒜ᶜˢ : Set (Finset (Fin n))).Sized (n - r) := by simpa using h₂.compls
  have : n - 2 * r ≤ n - r := by
    rw [tsub_le_tsub_iff_left ‹r ≤ n›]
    exact Nat.le_mul_of_pos_left _ zero_lt_two
  have kk := kruskal_katona_lovasz_form ‹n - 2 * r ≤ n - r› ((tsub_le_tsub_iff_left ‹1 ≤ n›).2 h1r)
      tsub_le_self h𝒜bar z.le
  have : n - r - (n - 2 * r) = r := by omega
  rw [this] at kk
  have : n.choose r < #(𝒜 ∪ ∂^[n - 2 * r] 𝒜ᶜˢ) := by
    rw [card_union_of_disjoint ‹_›]
    convert lt_of_le_of_lt (add_le_add_left kk _) (add_lt_add_right size _) using 1
    convert Nat.choose_succ_succ _ _ using 3
    all_goals rwa [Nat.sub_one, Nat.succ_pred_eq_of_pos]
  apply this.not_le
  convert Set.Sized.card_le _
  · rw [Fintype.card_fin]
  rw [coe_union, Set.sized_union]
  refine ⟨‹_›, ?_⟩
  convert h𝒜bar.shadow_iterate
  omega
end Finset