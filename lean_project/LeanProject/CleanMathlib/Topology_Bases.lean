import Mathlib.Data.Set.Constructions
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
open Set Filter Function Topology
noncomputable section
namespace TopologicalSpace
universe u
variable {α : Type u} {β : Type*} [t : TopologicalSpace α] {B : Set (Set α)} {s : Set α}
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  sUnion_eq : ⋃₀ s = univ
  eq_generateFrom : t = generateFrom s
theorem IsTopologicalBasis.insert_empty {s : Set (Set α)} (h : IsTopologicalBasis s) :
    IsTopologicalBasis (insert ∅ s) := by
  refine ⟨?_, by rw [sUnion_insert, empty_union, h.sUnion_eq], ?_⟩
  · rintro t₁ (rfl | h₁) t₂ (rfl | h₂) x ⟨hx₁, hx₂⟩
    · cases hx₁
    · cases hx₁
    · cases hx₂
    · obtain ⟨t₃, h₃, hs⟩ := h.exists_subset_inter _ h₁ _ h₂ x ⟨hx₁, hx₂⟩
      exact ⟨t₃, .inr h₃, hs⟩
  · rw [h.eq_generateFrom]
    refine le_antisymm (le_generateFrom fun t => ?_) (generateFrom_anti <| subset_insert ∅ s)
    rintro (rfl | ht)
    · exact @isOpen_empty _ (generateFrom s)
    · exact .basic t ht
theorem IsTopologicalBasis.diff_empty {s : Set (Set α)} (h : IsTopologicalBasis s) :
    IsTopologicalBasis (s \ {∅}) := by
  refine ⟨?_, by rw [sUnion_diff_singleton_empty, h.sUnion_eq], ?_⟩
  · rintro t₁ ⟨h₁, -⟩ t₂ ⟨h₂, -⟩ x hx
    obtain ⟨t₃, h₃, hs⟩ := h.exists_subset_inter _ h₁ _ h₂ x hx
    exact ⟨t₃, ⟨h₃, Nonempty.ne_empty ⟨x, hs.1⟩⟩, hs⟩
  · rw [h.eq_generateFrom]
    refine le_antisymm (generateFrom_anti diff_subset) (le_generateFrom fun t ht => ?_)
    obtain rfl | he := eq_or_ne t ∅
    · exact @isOpen_empty _ (generateFrom _)
    · exact .basic t ⟨ht, he⟩
theorem isTopologicalBasis_of_subbasis {s : Set (Set α)} (hs : t = generateFrom s) :
    IsTopologicalBasis ((fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ s }) := by
  subst t; letI := generateFrom s
  refine ⟨?_, ?_, le_antisymm (le_generateFrom ?_) <| generateFrom_anti fun t ht => ?_⟩
  · rintro _ ⟨t₁, ⟨hft₁, ht₁b⟩, rfl⟩ _ ⟨t₂, ⟨hft₂, ht₂b⟩, rfl⟩ x h
    exact ⟨_, ⟨_, ⟨hft₁.union hft₂, union_subset ht₁b ht₂b⟩, sInter_union t₁ t₂⟩, h, Subset.rfl⟩
  · rw [sUnion_image, iUnion₂_eq_univ_iff]
    exact fun x => ⟨∅, ⟨finite_empty, empty_subset _⟩, sInter_empty.substr <| mem_univ x⟩
  · rintro _ ⟨t, ⟨hft, htb⟩, rfl⟩
    exact hft.isOpen_sInter fun s hs ↦ GenerateOpen.basic _ <| htb hs
  · rw [← sInter_singleton t]
    exact ⟨{t}, ⟨finite_singleton t, singleton_subset_iff.2 ht⟩, rfl⟩
theorem isTopologicalBasis_of_subbasis_of_finiteInter {s : Set (Set α)} (hsg : t = generateFrom s)
    (hsi : FiniteInter s) : IsTopologicalBasis s := by
  convert isTopologicalBasis_of_subbasis hsg
  refine le_antisymm (fun t ht ↦ ⟨{t}, by simpa using ht⟩) ?_
  rintro _ ⟨g, ⟨hg, hgs⟩, rfl⟩
  lift g to Finset (Set α) using hg
  exact hsi.finiteInter_mem g hgs
theorem isTopologicalBasis_of_subbasis_of_inter {r : Set (Set α)} (hsg : t = generateFrom r)
    (hsi : ∀ ⦃s⦄, s ∈ r → ∀ ⦃t⦄, t ∈ r → s ∩ t ∈ r) : IsTopologicalBasis (insert univ r) :=
  isTopologicalBasis_of_subbasis_of_finiteInter (by simpa using hsg) (FiniteInter.mk₂ hsi)
theorem IsTopologicalBasis.of_hasBasis_nhds {s : Set (Set α)}
    (h_nhds : ∀ a, (𝓝 a).HasBasis (fun t ↦ t ∈ s ∧ a ∈ t) id) : IsTopologicalBasis s where
  exists_subset_inter t₁ ht₁ t₂ ht₂ x hx := by
    simpa only [and_assoc, (h_nhds x).mem_iff]
      using (inter_mem ((h_nhds _).mem_of_mem ⟨ht₁, hx.1⟩) ((h_nhds _).mem_of_mem ⟨ht₂, hx.2⟩))
  sUnion_eq := sUnion_eq_univ_iff.2 fun x ↦ (h_nhds x).ex_mem
  eq_generateFrom := ext_nhds fun x ↦ by
    simpa only [nhds_generateFrom, and_comm] using (h_nhds x).eq_biInf
theorem isTopologicalBasis_of_isOpen_of_nhds {s : Set (Set α)} (h_open : ∀ u ∈ s, IsOpen u)
    (h_nhds : ∀ (a : α) (u : Set α), a ∈ u → IsOpen u → ∃ v ∈ s, a ∈ v ∧ v ⊆ u) :
    IsTopologicalBasis s :=
  .of_hasBasis_nhds <| fun a ↦
    (nhds_basis_opens a).to_hasBasis' (by simpa [and_assoc] using h_nhds a)
      fun _ ⟨hts, hat⟩ ↦ (h_open _ hts).mem_nhds hat
theorem IsTopologicalBasis.mem_nhds_iff {a : α} {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) : s ∈ 𝓝 a ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s := by
  change s ∈ (𝓝 a).sets ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s
  rw [hb.eq_generateFrom, nhds_generateFrom, biInf_sets_eq]
  · simp [and_assoc, and_left_comm]
  · rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
    let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ ⟨hs₁, ht₁⟩
    exact ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (hu₃.trans inter_subset_left),
      le_principal_iff.2 (hu₃.trans inter_subset_right)⟩
  · rcases eq_univ_iff_forall.1 hb.sUnion_eq a with ⟨i, h1, h2⟩
    exact ⟨i, h2, h1⟩
theorem IsTopologicalBasis.isOpen_iff {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b) :
    IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ b, a ∈ t ∧ t ⊆ s := by simp [isOpen_iff_mem_nhds, hb.mem_nhds_iff]
theorem IsTopologicalBasis.nhds_hasBasis {b : Set (Set α)} (hb : IsTopologicalBasis b) {a : α} :
    (𝓝 a).HasBasis (fun t : Set α => t ∈ b ∧ a ∈ t) fun t => t :=
  ⟨fun s => hb.mem_nhds_iff.trans <| by simp only [and_assoc]⟩
protected theorem IsTopologicalBasis.isOpen {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hs : s ∈ b) : IsOpen s := by
  rw [hb.eq_generateFrom]
  exact .basic s hs
protected theorem IsTopologicalBasis.mem_nhds {a : α} {s : Set α} {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hs : s ∈ b) (ha : a ∈ s) : s ∈ 𝓝 a :=
  (hb.isOpen hs).mem_nhds ha
theorem IsTopologicalBasis.exists_subset_of_mem_open {b : Set (Set α)} (hb : IsTopologicalBasis b)
    {a : α} {u : Set α} (au : a ∈ u) (ou : IsOpen u) : ∃ v ∈ b, a ∈ v ∧ v ⊆ u :=
  hb.mem_nhds_iff.1 <| IsOpen.mem_nhds ou au
theorem IsTopologicalBasis.open_eq_sUnion' {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : u = ⋃₀ { s ∈ B | s ⊆ u } :=
  ext fun _a =>
    ⟨fun ha =>
      let ⟨b, hb, ab, bu⟩ := hB.exists_subset_of_mem_open ha ou
      ⟨b, ⟨hb, bu⟩, ab⟩,
      fun ⟨_b, ⟨_, bu⟩, ab⟩ => bu ab⟩
theorem IsTopologicalBasis.open_eq_sUnion {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : ∃ S ⊆ B, u = ⋃₀ S :=
  ⟨{ s ∈ B | s ⊆ u }, fun _ h => h.1, hB.open_eq_sUnion' ou⟩
theorem IsTopologicalBasis.open_iff_eq_sUnion {B : Set (Set α)} (hB : IsTopologicalBasis B)
    {u : Set α} : IsOpen u ↔ ∃ S ⊆ B, u = ⋃₀ S :=
  ⟨hB.open_eq_sUnion, fun ⟨_S, hSB, hu⟩ => hu.symm ▸ isOpen_sUnion fun _s hs => hB.isOpen (hSB hs)⟩
theorem IsTopologicalBasis.open_eq_iUnion {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α}
    (ou : IsOpen u) : ∃ (β : Type u) (f : β → Set α), (u = ⋃ i, f i) ∧ ∀ i, f i ∈ B :=
  ⟨↥({ s ∈ B | s ⊆ u }), (↑), by
    rw [← sUnion_eq_iUnion]
    apply hB.open_eq_sUnion' ou, fun s => And.left s.2⟩
lemma IsTopologicalBasis.subset_of_forall_subset {t : Set α} (hB : IsTopologicalBasis B)
    (hs : IsOpen s) (h : ∀ U ∈ B, U ⊆ s → U ⊆ t) : s ⊆ t := by
  rw [hB.open_eq_sUnion' hs]; simpa [sUnion_subset_iff]
lemma IsTopologicalBasis.eq_of_forall_subset_iff {t : Set α} (hB : IsTopologicalBasis B)
    (hs : IsOpen s) (ht : IsOpen t) (h : ∀ U ∈ B, U ⊆ s ↔ U ⊆ t) : s = t := by
  rw [hB.open_eq_sUnion' hs, hB.open_eq_sUnion' ht]
  exact congr_arg _ (Set.ext fun U ↦ and_congr_right <| h _)
theorem IsTopologicalBasis.mem_closure_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α}
    {a : α} : a ∈ closure s ↔ ∀ o ∈ b, a ∈ o → (o ∩ s).Nonempty :=
  (mem_closure_iff_nhds_basis' hb.nhds_hasBasis).trans <| by simp only [and_imp]
theorem IsTopologicalBasis.dense_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α} :
    Dense s ↔ ∀ o ∈ b, Set.Nonempty o → (o ∩ s).Nonempty := by
  simp only [Dense, hb.mem_closure_iff]
  exact ⟨fun h o hb ⟨a, ha⟩ => h a o hb ha, fun h a o hb ha => h o hb ⟨a, ha⟩⟩
theorem IsTopologicalBasis.isOpenMap_iff {β} [TopologicalSpace β] {B : Set (Set α)}
    (hB : IsTopologicalBasis B) {f : α → β} : IsOpenMap f ↔ ∀ s ∈ B, IsOpen (f '' s) := by
  refine ⟨fun H o ho => H _ (hB.isOpen ho), fun hf o ho => ?_⟩
  rw [hB.open_eq_sUnion' ho, sUnion_eq_iUnion, image_iUnion]
  exact isOpen_iUnion fun s => hf s s.2.1
theorem IsTopologicalBasis.exists_nonempty_subset {B : Set (Set α)} (hb : IsTopologicalBasis B)
    {u : Set α} (hu : u.Nonempty) (ou : IsOpen u) : ∃ v ∈ B, Set.Nonempty v ∧ v ⊆ u :=
  let ⟨x, hx⟩ := hu
  let ⟨v, vB, xv, vu⟩ := hb.exists_subset_of_mem_open hx ou
  ⟨v, vB, ⟨x, xv⟩, vu⟩
theorem isTopologicalBasis_opens : IsTopologicalBasis { U : Set α | IsOpen U } :=
  isTopologicalBasis_of_isOpen_of_nhds (by tauto) (by tauto)
protected lemma IsTopologicalBasis.isInducing {β} [TopologicalSpace β] {f : α → β} {T : Set (Set β)}
    (hf : IsInducing f) (h : IsTopologicalBasis T) : IsTopologicalBasis ((preimage f) '' T) :=
  .of_hasBasis_nhds fun a ↦ by
    convert (hf.basis_nhds (h.nhds_hasBasis (a := f a))).to_image_id with s
    aesop
@[deprecated (since := "2024-10-28")]
alias IsTopologicalBasis.inducing := IsTopologicalBasis.isInducing
protected theorem IsTopologicalBasis.induced {α} [s : TopologicalSpace β] (f : α → β)
    {T : Set (Set β)} (h : IsTopologicalBasis T) :
    IsTopologicalBasis (t := induced f s) ((preimage f) '' T) :=
  h.isInducing (t := induced f s) (.induced f)
protected theorem IsTopologicalBasis.inf {t₁ t₂ : TopologicalSpace β} {B₁ B₂ : Set (Set β)}
    (h₁ : IsTopologicalBasis (t := t₁) B₁) (h₂ : IsTopologicalBasis (t := t₂) B₂) :
    IsTopologicalBasis (t := t₁ ⊓ t₂) (image2 (· ∩ ·) B₁ B₂) := by
  refine .of_hasBasis_nhds (t := ?_) fun a ↦ ?_
  rw [nhds_inf (t₁ := t₁)]
  convert ((h₁.nhds_hasBasis (t := t₁)).inf (h₂.nhds_hasBasis (t := t₂))).to_image_id
  aesop
theorem IsTopologicalBasis.inf_induced {γ} [s : TopologicalSpace β] {B₁ : Set (Set α)}
    {B₂ : Set (Set β)} (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) (f₁ : γ → α)
    (f₂ : γ → β) :
    IsTopologicalBasis (t := induced f₁ t ⊓ induced f₂ s) (image2 (f₁ ⁻¹' · ∩ f₂ ⁻¹' ·) B₁ B₂) := by
  simpa only [image2_image_left, image2_image_right] using (h₁.induced f₁).inf (h₂.induced f₂)
protected theorem IsTopologicalBasis.prod {β} [TopologicalSpace β] {B₁ : Set (Set α)}
    {B₂ : Set (Set β)} (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis (image2 (· ×ˢ ·) B₁ B₂) :=
  h₁.inf_induced h₂ Prod.fst Prod.snd
theorem isTopologicalBasis_of_cover {ι} {U : ι → Set α} (Uo : ∀ i, IsOpen (U i))
    (Uc : ⋃ i, U i = univ) {b : ∀ i, Set (Set (U i))} (hb : ∀ i, IsTopologicalBasis (b i)) :
    IsTopologicalBasis (⋃ i : ι, image ((↑) : U i → α) '' b i) := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => ?_) ?_
  · simp only [mem_iUnion, mem_image] at hu
    rcases hu with ⟨i, s, sb, rfl⟩
    exact (Uo i).isOpenMap_subtype_val _ ((hb i).isOpen sb)
  · intro a u ha uo
    rcases iUnion_eq_univ_iff.1 Uc a with ⟨i, hi⟩
    lift a to ↥(U i) using hi
    rcases (hb i).exists_subset_of_mem_open ha (uo.preimage continuous_subtype_val) with
      ⟨v, hvb, hav, hvu⟩
    exact ⟨(↑) '' v, mem_iUnion.2 ⟨i, mem_image_of_mem _ hvb⟩, mem_image_of_mem _ hav,
      image_subset_iff.2 hvu⟩
protected theorem IsTopologicalBasis.continuous_iff {β : Type*} [TopologicalSpace β]
    {B : Set (Set β)} (hB : IsTopologicalBasis B) {f : α → β} :
    Continuous f ↔ ∀ s ∈ B, IsOpen (f ⁻¹' s) := by
  rw [hB.eq_generateFrom, continuous_generateFrom_iff]
variable (α)
@[mk_iff] class SeparableSpace : Prop where
  exists_countable_dense : ∃ s : Set α, s.Countable ∧ Dense s
theorem exists_countable_dense [SeparableSpace α] : ∃ s : Set α, s.Countable ∧ Dense s :=
  SeparableSpace.exists_countable_dense
theorem exists_dense_seq [SeparableSpace α] [Nonempty α] : ∃ u : ℕ → α, DenseRange u := by
  obtain ⟨s : Set α, hs, s_dense⟩ := exists_countable_dense α
  cases' Set.countable_iff_exists_subset_range.mp hs with u hu
  exact ⟨u, s_dense.mono hu⟩
def denseSeq [SeparableSpace α] [Nonempty α] : ℕ → α :=
  Classical.choose (exists_dense_seq α)
@[simp]
theorem denseRange_denseSeq [SeparableSpace α] [Nonempty α] : DenseRange (denseSeq α) :=
  Classical.choose_spec (exists_dense_seq α)
variable {α}
instance (priority := 100) Countable.to_separableSpace [Countable α] : SeparableSpace α where
  exists_countable_dense := ⟨Set.univ, Set.countable_univ, dense_univ⟩
theorem SeparableSpace.of_denseRange {ι : Sort _} [Countable ι] (u : ι → α) (hu : DenseRange u) :
    SeparableSpace α :=
  ⟨⟨range u, countable_range u, hu⟩⟩
alias _root_.DenseRange.separableSpace' := SeparableSpace.of_denseRange
protected theorem _root_.DenseRange.separableSpace [SeparableSpace α] [TopologicalSpace β]
    {f : α → β} (h : DenseRange f) (h' : Continuous f) : SeparableSpace β :=
  let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α
  ⟨⟨f '' s, Countable.image s_cnt f, h.dense_image h' s_dense⟩⟩
theorem _root_.Topology.IsQuotientMap.separableSpace [SeparableSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsQuotientMap f) : SeparableSpace β :=
  hf.surjective.denseRange.separableSpace hf.continuous
@[deprecated (since := "2024-10-22")]
alias _root_.QuotientMap.separableSpace := Topology.IsQuotientMap.separableSpace
instance [TopologicalSpace β] [SeparableSpace α] [SeparableSpace β] : SeparableSpace (α × β) := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  rcases exists_countable_dense β with ⟨t, htc, htd⟩
  exact ⟨⟨s ×ˢ t, hsc.prod htc, hsd.prod htd⟩⟩
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, SeparableSpace (X i)]
    [Countable ι] : SeparableSpace (∀ i, X i) := by
  choose t htc htd using (exists_countable_dense <| X ·)
  haveI := fun i ↦ (htc i).to_subtype
  nontriviality ∀ i, X i; inhabit ∀ i, X i
  classical
    set f : (Σ I : Finset ι, ∀ i : I, t i) → ∀ i, X i := fun ⟨I, g⟩ i ↦
      if hi : i ∈ I then g ⟨i, hi⟩ else (default : ∀ i, X i) i
    refine ⟨⟨range f, countable_range f, dense_iff_inter_open.2 fun U hU ⟨g, hg⟩ ↦ ?_⟩⟩
    rcases isOpen_pi_iff.1 hU g hg with ⟨I, u, huo, huU⟩
    have : ∀ i : I, ∃ y ∈ t i, y ∈ u i := fun i ↦
      (htd i).exists_mem_open (huo i i.2).1 ⟨_, (huo i i.2).2⟩
    choose y hyt hyu using this
    lift y to ∀ i : I, t i using hyt
    refine ⟨f ⟨I, y⟩, huU fun i (hi : i ∈ I) ↦ ?_, mem_range_self (f := f) ⟨I, y⟩⟩
    simp only [f, dif_pos hi]
    exact hyu ⟨i, _⟩
instance [SeparableSpace α] {r : α → α → Prop} : SeparableSpace (Quot r) :=
  isQuotientMap_quot_mk.separableSpace
instance [SeparableSpace α] {s : Setoid α} : SeparableSpace (Quotient s) :=
  isQuotientMap_quot_mk.separableSpace
theorem separableSpace_iff_countable [DiscreteTopology α] : SeparableSpace α ↔ Countable α := by
  simp [separableSpace_iff, countable_univ_iff]
theorem _root_.Pairwise.countable_of_isOpen_disjoint [SeparableSpace α] {ι : Type*}
    {s : ι → Set α} (hd : Pairwise (Disjoint on s)) (ho : ∀ i, IsOpen (s i))
    (hne : ∀ i, (s i).Nonempty) : Countable ι := by
  rcases exists_countable_dense α with ⟨u, u_countable, u_dense⟩
  choose f hfu hfs using fun i ↦ u_dense.exists_mem_open (ho i) (hne i)
  have f_inj : Injective f := fun i j hij ↦
    hd.eq <| not_disjoint_iff.2 ⟨f i, hfs i, hij.symm ▸ hfs j⟩
  have := u_countable.to_subtype
  exact (f_inj.codRestrict hfu).countable
theorem _root_.Set.PairwiseDisjoint.countable_of_isOpen [SeparableSpace α] {ι : Type*}
    {s : ι → Set α} {a : Set ι} (h : a.PairwiseDisjoint s) (ho : ∀ i ∈ a, IsOpen (s i))
    (hne : ∀ i ∈ a, (s i).Nonempty) : a.Countable :=
  (h.subtype _ _).countable_of_isOpen_disjoint (Subtype.forall.2 ho) (Subtype.forall.2 hne)
theorem _root_.Set.PairwiseDisjoint.countable_of_nonempty_interior [SeparableSpace α] {ι : Type*}
    {s : ι → Set α} {a : Set ι} (h : a.PairwiseDisjoint s)
    (ha : ∀ i ∈ a, (interior (s i)).Nonempty) : a.Countable :=
  (h.mono fun _ => interior_subset).countable_of_isOpen (fun _ _ => isOpen_interior) ha
def IsSeparable (s : Set α) :=
  ∃ c : Set α, c.Countable ∧ s ⊆ closure c
theorem IsSeparable.mono {s u : Set α} (hs : IsSeparable s) (hu : u ⊆ s) : IsSeparable u := by
  rcases hs with ⟨c, c_count, hs⟩
  exact ⟨c, c_count, hu.trans hs⟩
theorem IsSeparable.iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (hs : ∀ i, IsSeparable (s i)) : IsSeparable (⋃ i, s i) := by
  choose c hc h'c using hs
  refine ⟨⋃ i, c i, countable_iUnion hc, iUnion_subset_iff.2 fun i => ?_⟩
  exact (h'c i).trans (closure_mono (subset_iUnion _ i))
@[simp]
theorem isSeparable_iUnion {ι : Sort*} [Countable ι] {s : ι → Set α} :
    IsSeparable (⋃ i, s i) ↔ ∀ i, IsSeparable (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion s i, .iUnion⟩
@[simp]
theorem isSeparable_union {s t : Set α} : IsSeparable (s ∪ t) ↔ IsSeparable s ∧ IsSeparable t := by
  simp [union_eq_iUnion, and_comm]
theorem IsSeparable.union {s u : Set α} (hs : IsSeparable s) (hu : IsSeparable u) :
    IsSeparable (s ∪ u) :=
  isSeparable_union.2 ⟨hs, hu⟩
@[simp]
theorem isSeparable_closure : IsSeparable (closure s) ↔ IsSeparable s := by
  simp only [IsSeparable, isClosed_closure.closure_subset_iff]
protected alias ⟨_, IsSeparable.closure⟩ := isSeparable_closure
theorem _root_.Set.Countable.isSeparable {s : Set α} (hs : s.Countable) : IsSeparable s :=
  ⟨s, hs, subset_closure⟩
theorem _root_.Set.Finite.isSeparable {s : Set α} (hs : s.Finite) : IsSeparable s :=
  hs.countable.isSeparable
theorem IsSeparable.univ_pi {ι : Type*} [Countable ι] {X : ι → Type*} {s : ∀ i, Set (X i)}
    [∀ i, TopologicalSpace (X i)] (h : ∀ i, IsSeparable (s i)) :
    IsSeparable (univ.pi s) := by
  classical
  rcases eq_empty_or_nonempty (univ.pi s) with he | ⟨f₀, -⟩
  · rw [he]
    exact countable_empty.isSeparable
  · choose c c_count hc using h
    haveI := fun i ↦ (c_count i).to_subtype
    set g : (I : Finset ι) × ((i : I) → c i) → (i : ι) → X i := fun ⟨I, f⟩ i ↦
      if hi : i ∈ I then f ⟨i, hi⟩ else f₀ i
    refine ⟨range g, countable_range g, fun f hf ↦ mem_closure_iff.2 fun o ho hfo ↦ ?_⟩
    rcases isOpen_pi_iff.1 ho f hfo with ⟨I, u, huo, hI⟩
    rsuffices ⟨f, hf⟩ : ∃ f : (i : I) → c i, g ⟨I, f⟩ ∈ Set.pi I u
    · exact ⟨g ⟨I, f⟩, hI hf, mem_range_self (f := g) ⟨I, f⟩⟩
    suffices H : ∀ i ∈ I, (u i ∩ c i).Nonempty by
      choose f hfu hfc using H
      refine ⟨fun i ↦ ⟨f i i.2, hfc i i.2⟩, fun i (hi : i ∈ I) ↦ ?_⟩
      simpa only [g, dif_pos hi] using hfu i hi
    intro i hi
    exact mem_closure_iff.1 (hc i <| hf _ trivial) _ (huo i hi).1 (huo i hi).2
lemma isSeparable_pi {ι : Type*} [Countable ι] {α : ι → Type*} {s : ∀ i, Set (α i)}
    [∀ i, TopologicalSpace (α i)] (h : ∀ i, IsSeparable (s i)) :
    IsSeparable {f : ∀ i, α i | ∀ i, f i ∈ s i} := by
  simpa only [← mem_univ_pi] using IsSeparable.univ_pi h
lemma IsSeparable.prod {β : Type*} [TopologicalSpace β]
    {s : Set α} {t : Set β} (hs : IsSeparable s) (ht : IsSeparable t) :
    IsSeparable (s ×ˢ t) := by
  rcases hs with ⟨cs, cs_count, hcs⟩
  rcases ht with ⟨ct, ct_count, hct⟩
  refine ⟨cs ×ˢ ct, cs_count.prod ct_count, ?_⟩
  rw [closure_prod_eq]
  gcongr
theorem IsSeparable.image {β : Type*} [TopologicalSpace β] {s : Set α} (hs : IsSeparable s)
    {f : α → β} (hf : Continuous f) : IsSeparable (f '' s) := by
  rcases hs with ⟨c, c_count, hc⟩
  refine ⟨f '' c, c_count.image _, ?_⟩
  rw [image_subset_iff]
  exact hc.trans (closure_subset_preimage_closure_image hf)
theorem _root_.Dense.isSeparable_iff (hs : Dense s) :
    IsSeparable s ↔ SeparableSpace α := by
  simp_rw [IsSeparable, separableSpace_iff, dense_iff_closure_eq, ← univ_subset_iff,
    ← hs.closure_eq, isClosed_closure.closure_subset_iff]
theorem isSeparable_univ_iff : IsSeparable (univ : Set α) ↔ SeparableSpace α :=
  dense_univ.isSeparable_iff
theorem isSeparable_range [TopologicalSpace β] [SeparableSpace α] {f : α → β} (hf : Continuous f) :
    IsSeparable (range f) :=
  image_univ (f := f) ▸ (isSeparable_univ_iff.2 ‹_›).image hf
theorem IsSeparable.of_subtype (s : Set α) [SeparableSpace s] : IsSeparable s := by
  simpa using isSeparable_range (continuous_subtype_val (p := (· ∈ s)))
@[deprecated (since := "2024-02-05")]
alias isSeparable_of_separableSpace_subtype := IsSeparable.of_subtype
theorem IsSeparable.of_separableSpace [h : SeparableSpace α] (s : Set α) : IsSeparable s :=
  IsSeparable.mono (isSeparable_univ_iff.2 h) (subset_univ _)
@[deprecated (since := "2024-02-05")]
alias isSeparable_of_separableSpace := IsSeparable.of_separableSpace
end TopologicalSpace
open TopologicalSpace
protected theorem IsTopologicalBasis.iInf {β : Type*} {ι : Type*} {t : ι → TopologicalSpace β}
    {T : ι → Set (Set β)} (h_basis : ∀ i, IsTopologicalBasis (t := t i) (T i)) :
    IsTopologicalBasis (t := ⨅ i, t i)
      { S | ∃ (U : ι → Set β) (F : Finset ι), (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ i ∈ F, U i } := by
  let _ := ⨅ i, t i
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro - ⟨U, F, hU, rfl⟩
    refine isOpen_biInter_finset fun i hi ↦
      (h_basis i).isOpen (t := t i) (hU i hi) |>.mono (iInf_le _ _)
  · intro a u ha hu
    rcases (nhds_iInf (t := t) (a := a)).symm ▸ hasBasis_iInf'
      (fun i ↦ (h_basis i).nhds_hasBasis (t := t i)) |>.mem_iff.1 (hu.mem_nhds ha)
      with ⟨⟨F, U⟩, ⟨hF, hU⟩, hUu⟩
    refine ⟨_, ⟨U, hF.toFinset, ?_, rfl⟩, ?_, ?_⟩ <;> simp only [Finite.mem_toFinset, mem_iInter]
    · exact fun i hi ↦ (hU i hi).1
    · exact fun i hi ↦ (hU i hi).2
    · exact hUu
theorem IsTopologicalBasis.iInf_induced {β : Type*} {ι : Type*} {X : ι → Type*}
    [t : Π i, TopologicalSpace (X i)] {T : Π i, Set (Set (X i))}
    (cond : ∀ i, IsTopologicalBasis (T i)) (f : Π i, β → X i) :
    IsTopologicalBasis (t := ⨅ i, induced (f i) (t i))
      { S | ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
        (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ (i) (_ : i ∈ F), f i ⁻¹' U i } := by
  convert IsTopologicalBasis.iInf (fun i ↦ (cond i).induced (f i)) with S
  constructor <;> rintro ⟨U, F, hUT, hSU⟩
  · exact ⟨fun i ↦ (f i) ⁻¹' (U i), F, fun i hi ↦ mem_image_of_mem _ (hUT i hi), hSU⟩
  · choose! U' hU' hUU' using hUT
    exact ⟨U', F, hU', hSU ▸ (.symm <| iInter₂_congr hUU')⟩
theorem isTopologicalBasis_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {T : ∀ i, Set (Set (X i))} (cond : ∀ i, IsTopologicalBasis (T i)) :
    IsTopologicalBasis { S | ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
      (∀ i, i ∈ F → U i ∈ T i) ∧ S = (F : Set ι).pi U } := by
  simpa only [Set.pi_def] using IsTopologicalBasis.iInf_induced cond eval
theorem isTopologicalBasis_singletons (α : Type*) [TopologicalSpace α] [DiscreteTopology α] :
    IsTopologicalBasis { s | ∃ x : α, (s : Set α) = {x} } :=
  isTopologicalBasis_of_isOpen_of_nhds (fun _ _ => isOpen_discrete _) fun x _ hx _ =>
    ⟨{x}, ⟨x, rfl⟩, mem_singleton x, singleton_subset_iff.2 hx⟩
theorem isTopologicalBasis_subtype
    {α : Type*} [TopologicalSpace α] {B : Set (Set α)}
    (h : TopologicalSpace.IsTopologicalBasis B) (p : α → Prop) :
    IsTopologicalBasis (Set.preimage (Subtype.val (p := p)) '' B) :=
  h.isInducing ⟨rfl⟩
section
variable {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
lemma isOpenMap_eval (i : ι) : IsOpenMap (Function.eval i : (∀ i, π i) → π i) := by
  classical
  refine (isTopologicalBasis_pi fun _ ↦ isTopologicalBasis_opens).isOpenMap_iff.2 ?_
  rintro _ ⟨U, s, hU, rfl⟩
  obtain h | h := ((s : Set ι).pi U).eq_empty_or_nonempty
  · simp [h]
  by_cases hi : i ∈ s
  · rw [eval_image_pi (mod_cast hi) h]
    exact hU _ hi
  · rw [eval_image_pi_of_not_mem (mod_cast hi), if_pos h]
    exact isOpen_univ
end
theorem Dense.exists_countable_dense_subset {α : Type*} [TopologicalSpace α] {s : Set α}
    [SeparableSpace s] (hs : Dense s) : ∃ t ⊆ s, t.Countable ∧ Dense t :=
  let ⟨t, htc, htd⟩ := exists_countable_dense s
  ⟨(↑) '' t, Subtype.coe_image_subset s t, htc.image Subtype.val,
    hs.denseRange_val.dense_image continuous_subtype_val htd⟩
theorem Dense.exists_countable_dense_subset_bot_top {α : Type*} [TopologicalSpace α]
    [PartialOrder α] {s : Set α} [SeparableSpace s] (hs : Dense s) :
    ∃ t ⊆ s, t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∈ s → x ∈ t) ∧
      ∀ x, IsTop x → x ∈ s → x ∈ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨(t ∪ ({ x | IsBot x } ∪ { x | IsTop x })) ∩ s, ?_, ?_, ?_, ?_, ?_⟩
  exacts [inter_subset_right,
    (htc.union ((countable_isBot α).union (countable_isTop α))).mono inter_subset_left,
    htd.mono (subset_inter subset_union_left hts), fun x hx hxs => ⟨Or.inr <| Or.inl hx, hxs⟩,
    fun x hx hxs => ⟨Or.inr <| Or.inr hx, hxs⟩]
instance separableSpace_univ {α : Type*} [TopologicalSpace α] [SeparableSpace α] :
    SeparableSpace (univ : Set α) :=
  (Equiv.Set.univ α).symm.surjective.denseRange.separableSpace (continuous_id.subtype_mk _)
theorem exists_countable_dense_bot_top (α : Type*) [TopologicalSpace α] [SeparableSpace α]
    [PartialOrder α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∈ s) ∧ ∀ x, IsTop x → x ∈ s := by
  simpa using dense_univ.exists_countable_dense_subset_bot_top
namespace TopologicalSpace
universe u
variable (α : Type u) [t : TopologicalSpace α]
class _root_.FirstCountableTopology : Prop where
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated
attribute [instance] FirstCountableTopology.nhds_generated_countable
theorem firstCountableTopology_induced (α β : Type*) [t : TopologicalSpace β]
    [FirstCountableTopology β] (f : α → β) : @FirstCountableTopology α (t.induced f) :=
  let _ := t.induced f
  ⟨fun x ↦ nhds_induced f x ▸ inferInstance⟩
variable {α}
instance Subtype.firstCountableTopology (s : Set α) [FirstCountableTopology α] :
    FirstCountableTopology s :=
  firstCountableTopology_induced s α (↑)
protected theorem _root_.Topology.IsInducing.firstCountableTopology {β : Type*}
    [TopologicalSpace β] [FirstCountableTopology β] {f : α → β} (hf : IsInducing f) :
    FirstCountableTopology α := by
  rw [hf.1]
  exact firstCountableTopology_induced α β f
@[deprecated (since := "2024-10-28")]
alias _root_.Inducing.firstCountableTopology := IsInducing.firstCountableTopology
protected theorem _root_.Topology.IsEmbedding.firstCountableTopology {β : Type*}
    [TopologicalSpace β] [FirstCountableTopology β] {f : α → β} (hf : IsEmbedding f) :
    FirstCountableTopology α :=
  hf.1.firstCountableTopology
@[deprecated (since := "2024-10-26")]
alias _root_.Embedding.firstCountableTopology := IsEmbedding.firstCountableTopology
namespace FirstCountableTopology
theorem tendsto_subseq [FirstCountableTopology α] {u : ℕ → α} {x : α}
    (hx : MapClusterPt x atTop u) : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x) :=
  subseq_tendsto_of_neBot hx
end FirstCountableTopology
instance {β} [TopologicalSpace β] [FirstCountableTopology α] [FirstCountableTopology β] :
    FirstCountableTopology (α × β) :=
  ⟨fun ⟨x, y⟩ => by rw [nhds_prod_eq]; infer_instance⟩
section Pi
instance {ι : Type*} {π : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (π i)]
    [∀ i, FirstCountableTopology (π i)] : FirstCountableTopology (∀ i, π i) :=
  ⟨fun f => by rw [nhds_pi]; infer_instance⟩
end Pi
instance isCountablyGenerated_nhdsWithin (x : α) [IsCountablyGenerated (𝓝 x)] (s : Set α) :
    IsCountablyGenerated (𝓝[s] x) :=
  Inf.isCountablyGenerated _ _
variable (α)
class _root_.SecondCountableTopology : Prop where
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
variable {α}
protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩
lemma SecondCountableTopology.mk' {α} {b : Set (Set α)} (hc : b.Countable) :
    @SecondCountableTopology α (generateFrom b) :=
  @SecondCountableTopology.mk α (generateFrom b) ⟨b, hc, rfl⟩
instance _root_.Finite.toSecondCountableTopology [Finite α] : SecondCountableTopology α where
  is_open_generated_countable :=
    ⟨_, {U | IsOpen U}.to_countable, TopologicalSpace.isTopologicalBasis_opens.eq_generateFrom⟩
variable (α)
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, not_mem_diff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).diff_empty⟩
  exacts [((countable_setOf_finite_subset hb₁).image _).mono diff_subset, rfl]
def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).choose
theorem countable_countableBasis [SecondCountableTopology α] : (countableBasis α).Countable :=
  (exists_countable_basis α).choose_spec.1
instance encodableCountableBasis [SecondCountableTopology α] : Encodable (countableBasis α) :=
  (countable_countableBasis α).toEncodable
theorem empty_nmem_countableBasis [SecondCountableTopology α] : ∅ ∉ countableBasis α :=
  (exists_countable_basis α).choose_spec.2.1
theorem isBasis_countableBasis [SecondCountableTopology α] :
    IsTopologicalBasis (countableBasis α) :=
  (exists_countable_basis α).choose_spec.2.2
theorem eq_generateFrom_countableBasis [SecondCountableTopology α] :
    ‹TopologicalSpace α› = generateFrom (countableBasis α) :=
  (isBasis_countableBasis α).eq_generateFrom
variable {α}
theorem isOpen_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : IsOpen s :=
  (isBasis_countableBasis α).isOpen hs
theorem nonempty_of_mem_countableBasis [SecondCountableTopology α] {s : Set α}
    (hs : s ∈ countableBasis α) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs <| empty_nmem_countableBasis α
variable (α)
instance (priority := 100) SecondCountableTopology.to_firstCountableTopology
    [SecondCountableTopology α] : FirstCountableTopology α :=
  ⟨fun _ => HasCountableBasis.isCountablyGenerated <|
      ⟨(isBasis_countableBasis α).nhds_hasBasis,
        (countable_countableBasis α).mono inter_subset_left⟩⟩
theorem secondCountableTopology_induced (α β) [t : TopologicalSpace β] [SecondCountableTopology β]
    (f : α → β) : @SecondCountableTopology α (t.induced f) := by
  rcases @SecondCountableTopology.is_open_generated_countable β _ _ with ⟨b, hb, eq⟩
  letI := t.induced f
  refine { is_open_generated_countable := ⟨preimage f '' b, hb.image _, ?_⟩ }
  rw [eq, induced_generateFrom_eq]
variable {α}
instance Subtype.secondCountableTopology (s : Set α) [SecondCountableTopology α] :
    SecondCountableTopology s :=
  secondCountableTopology_induced s α (↑)
lemma secondCountableTopology_iInf {α ι} [Countable ι] {t : ι → TopologicalSpace α}
    (ht : ∀ i, @SecondCountableTopology α (t i)) : @SecondCountableTopology α (⨅ i, t i) := by
  rw [funext fun i => @eq_generateFrom_countableBasis α (t i) (ht i), ← generateFrom_iUnion]
  exact SecondCountableTopology.mk' <|
    countable_iUnion fun i => @countable_countableBasis _ (t i) (ht i)
instance {β : Type*} [TopologicalSpace β] [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α × β) :=
  ((isBasis_countableBasis α).prod (isBasis_countableBasis β)).secondCountableTopology <|
    (countable_countableBasis α).image2 (countable_countableBasis β) _
instance {ι : Type*} {π : ι → Type*} [Countable ι] [∀ a, TopologicalSpace (π a)]
    [∀ a, SecondCountableTopology (π a)] : SecondCountableTopology (∀ a, π a) :=
  secondCountableTopology_iInf fun _ => secondCountableTopology_induced _ _ _
instance (priority := 100) SecondCountableTopology.to_separableSpace [SecondCountableTopology α] :
    SeparableSpace α := by
  choose p hp using fun s : countableBasis α => nonempty_of_mem_countableBasis s.2
  exact ⟨⟨range p, countable_range _, (isBasis_countableBasis α).dense_iff.2 fun o ho _ =>
          ⟨p ⟨o, ho⟩, hp ⟨o, _⟩, mem_range_self _⟩⟩⟩
theorem secondCountableTopology_of_countable_cover {ι} [Countable ι] {U : ι → Set α}
    [∀ i, SecondCountableTopology (U i)] (Uo : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = univ) :
    SecondCountableTopology α :=
  haveI : IsTopologicalBasis (⋃ i, image ((↑) : U i → α) '' countableBasis (U i)) :=
    isTopologicalBasis_of_cover Uo hc fun i => isBasis_countableBasis (U i)
  this.secondCountableTopology (countable_iUnion fun _ => (countable_countableBasis _).image _)
theorem isOpen_iUnion_countable [SecondCountableTopology α] {ι} (s : ι → Set α)
    (H : ∀ i, IsOpen (s i)) : ∃ T : Set ι, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i, s i := by
  let B := { b ∈ countableBasis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  haveI : Countable B := ((countable_countableBasis α).mono (sep_subset _ _)).to_subtype
  refine ⟨_, countable_range f, (iUnion₂_subset_iUnion _ _).antisymm (sUnion_subset ?_)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases (isBasis_countableBasis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩
theorem isOpen_biUnion_countable [SecondCountableTopology α] {ι : Type*} (I : Set ι) (s : ι → Set α)
    (H : ∀ i ∈ I, IsOpen (s i)) : ∃ T ⊆ I, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i ∈ I, s i := by
  simp_rw [← Subtype.exists_set_subtype, biUnion_image]
  rcases isOpen_iUnion_countable (fun i : I ↦ s i) fun i ↦ H i i.2 with ⟨T, hTc, hU⟩
  exact ⟨T, hTc.image _, hU.trans <| iUnion_subtype ..⟩
theorem isOpen_sUnion_countable [SecondCountableTopology α] (S : Set (Set α))
    (H : ∀ s ∈ S, IsOpen s) : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S := by
  simpa only [and_left_comm, sUnion_eq_biUnion] using isOpen_biUnion_countable S id H
theorem countable_cover_nhds [SecondCountableTopology α] {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  rcases isOpen_iUnion_countable (fun x => interior (f x)) fun x => isOpen_interior with
    ⟨s, hsc, hsU⟩
  suffices ⋃ x ∈ s, interior (f x) = univ from
    ⟨s, hsc, flip eq_univ_of_subset this <| iUnion₂_mono fun _ _ => interior_subset⟩
  simp only [hsU, eq_univ_iff_forall, mem_iUnion]
  exact fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩
theorem countable_cover_nhdsWithin [SecondCountableTopology α] {f : α → Set α} {s : Set α}
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  have : ∀ x : s, (↑) ⁻¹' f x ∈ 𝓝 x := fun x => preimage_coe_mem_nhds_subtype.2 (hf x x.2)
  rcases countable_cover_nhds this with ⟨t, htc, htU⟩
  refine ⟨(↑) '' t, Subtype.coe_image_subset _ _, htc.image _, fun x hx => ?_⟩
  simp only [biUnion_image, eq_univ_iff_forall, ← preimage_iUnion, mem_preimage] at htU ⊢
  exact htU ⟨x, hx⟩
section Sigma
variable {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
theorem IsTopologicalBasis.sigma {s : ∀ i : ι, Set (Set (E i))}
    (hs : ∀ i, IsTopologicalBasis (s i)) :
    IsTopologicalBasis (⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' s i) := by
  refine .of_hasBasis_nhds fun a ↦ ?_
  rw [Sigma.nhds_eq]
  convert (((hs a.1).nhds_hasBasis).map _).to_image_id
  aesop
instance [Countable ι] [∀ i, SecondCountableTopology (E i)] :
    SecondCountableTopology (Σi, E i) := by
  let b := ⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' countableBasis (E i)
  have A : IsTopologicalBasis b := IsTopologicalBasis.sigma fun i => isBasis_countableBasis _
  have B : b.Countable := countable_iUnion fun i => (countable_countableBasis _).image _
  exact A.secondCountableTopology B
end Sigma
section Sum
variable {β : Type*} [TopologicalSpace β]
theorem IsTopologicalBasis.sum {s : Set (Set α)} (hs : IsTopologicalBasis s) {t : Set (Set β)}
    (ht : IsTopologicalBasis t) :
    IsTopologicalBasis ((fun u => Sum.inl '' u) '' s ∪ (fun u => Sum.inr '' u) '' t) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact IsOpenEmbedding.inl.isOpenMap w (hs.isOpen hw)
    · exact IsOpenEmbedding.inr.isOpenMap w (ht.isOpen hw)
  · rintro (x | x) u hxu u_open
    · obtain ⟨v, vs, xv, vu⟩ : ∃ v ∈ s, x ∈ v ∧ v ⊆ Sum.inl ⁻¹' u :=
        hs.exists_subset_of_mem_open hxu (isOpen_sum_iff.1 u_open).1
      exact ⟨Sum.inl '' v, mem_union_left _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv,
        image_subset_iff.2 vu⟩
    · obtain ⟨v, vs, xv, vu⟩ : ∃ v ∈ t, x ∈ v ∧ v ⊆ Sum.inr ⁻¹' u :=
        ht.exists_subset_of_mem_open hxu (isOpen_sum_iff.1 u_open).2
      exact ⟨Sum.inr '' v, mem_union_right _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv,
        image_subset_iff.2 vu⟩
instance [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α ⊕ β) := by
  let b :=
    (fun u => Sum.inl '' u) '' countableBasis α ∪ (fun u => Sum.inr '' u) '' countableBasis β
  have A : IsTopologicalBasis b := (isBasis_countableBasis α).sum (isBasis_countableBasis β)
  have B : b.Countable :=
    (Countable.image (countable_countableBasis _) _).union
      (Countable.image (countable_countableBasis _) _)
  exact A.secondCountableTopology B
end Sum
section Quotient
variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {π : X → Y}
theorem IsTopologicalBasis.isQuotientMap {V : Set (Set X)} (hV : IsTopologicalBasis V)
    (h' : IsQuotientMap π) (h : IsOpenMap π) : IsTopologicalBasis (Set.image π '' V) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro - ⟨U, U_in_V, rfl⟩
    apply h U (hV.isOpen U_in_V)
  · intro y U y_in_U U_open
    obtain ⟨x, rfl⟩ := h'.surjective y
    let W := π ⁻¹' U
    have x_in_W : x ∈ W := y_in_U
    have W_open : IsOpen W := U_open.preimage h'.continuous
    obtain ⟨Z, Z_in_V, x_in_Z, Z_in_W⟩ := hV.exists_subset_of_mem_open x_in_W W_open
    have πZ_in_U : π '' Z ⊆ U := (Set.image_subset _ Z_in_W).trans (image_preimage_subset π U)
    exact ⟨π '' Z, ⟨Z, Z_in_V, rfl⟩, ⟨x, x_in_Z, rfl⟩, πZ_in_U⟩
@[deprecated (since := "2024-10-22")]
alias IsTopologicalBasis.quotientMap := IsTopologicalBasis.isQuotientMap
theorem _root_.Topology.IsQuotientMap.secondCountableTopology [SecondCountableTopology X]
    (h' : IsQuotientMap π) (h : IsOpenMap π) : SecondCountableTopology Y where
  is_open_generated_countable := by
    obtain ⟨V, V_countable, -, V_generates⟩ := exists_countable_basis X
    exact ⟨Set.image π '' V, V_countable.image (Set.image π),
      (V_generates.isQuotientMap h' h).eq_generateFrom⟩
@[deprecated (since := "2024-10-22")]
alias _root_.QuotientMap.secondCountableTopology := IsQuotientMap.secondCountableTopology
variable {S : Setoid X}
theorem IsTopologicalBasis.quotient {V : Set (Set X)} (hV : IsTopologicalBasis V)
    (h : IsOpenMap (Quotient.mk' : X → Quotient S)) :
    IsTopologicalBasis (Set.image (Quotient.mk' : X → Quotient S) '' V) :=
  hV.isQuotientMap isQuotientMap_quotient_mk' h
theorem Quotient.secondCountableTopology [SecondCountableTopology X]
    (h : IsOpenMap (Quotient.mk' : X → Quotient S)) : SecondCountableTopology (Quotient S) :=
  isQuotientMap_quotient_mk'.secondCountableTopology h
end Quotient
end TopologicalSpace
open TopologicalSpace
variable {α β : Type*} [TopologicalSpace α] {f : α → β}
protected theorem Topology.IsInducing.secondCountableTopology [TopologicalSpace β]
    [SecondCountableTopology β] (hf : IsInducing f) : SecondCountableTopology α := by
  rw [hf.1]
  exact secondCountableTopology_induced α β f
@[deprecated (since := "2024-10-28")]
alias Inducing.secondCountableTopology := IsInducing.secondCountableTopology
protected theorem Topology.IsEmbedding.secondCountableTopology
    [TopologicalSpace β] [SecondCountableTopology β]
    (hf : IsEmbedding f) : SecondCountableTopology α :=
  hf.1.secondCountableTopology
protected theorem Topology.IsEmbedding.separableSpace
    [TopologicalSpace β] [SecondCountableTopology β] {f : α → β} (hf : IsEmbedding f) :
    TopologicalSpace.SeparableSpace α := by
  have := hf.secondCountableTopology
  exact SecondCountableTopology.to_separableSpace