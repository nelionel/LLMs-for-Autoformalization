import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone
open Filter OrderDual TopologicalSpace Function Set
open scoped Topology Filter Interval
universe u v
section
variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α]
theorem intermediate_value_univ₂ [PreconnectedSpace X] {a b : X} {f g : X → α} (hf : Continuous f)
    (hg : Continuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, _, hfg, hgf⟩ : (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty :=
    isPreconnected_closed_iff.1 PreconnectedSpace.isPreconnected_univ _ _ (isClosed_le hf hg)
      (isClosed_le hg hf) (fun _ _ => le_total _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩
theorem intermediate_value_univ₂_eventually₁ [PreconnectedSpace X] {a : X} {l : Filter X} [NeBot l]
    {f g : X → α} (hf : Continuous f) (hg : Continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) :
    ∃ x, f x = g x :=
  let ⟨_, h⟩ := he.exists; intermediate_value_univ₂ hf hg ha h
theorem intermediate_value_univ₂_eventually₂ [PreconnectedSpace X] {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] {f g : X → α} (hf : Continuous f) (hg : Continuous g) (he₁ : f ≤ᶠ[l₁] g)
    (he₂ : g ≤ᶠ[l₂] f) : ∃ x, f x = g x :=
  let ⟨_, h₁⟩ := he₁.exists
  let ⟨_, h₂⟩ := he₂.exists
  intermediate_value_univ₂ hf hg h₁ h₂
theorem IsPreconnected.intermediate_value₂ {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (ha' : f a ≤ g a) (hb' : g b ≤ f b) : ∃ x ∈ s, f x = g x :=
  let ⟨x, hx⟩ :=
    @intermediate_value_univ₂ s α _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ ⟨b, hb⟩ _ _
      (continuousOn_iff_continuous_restrict.1 hf) (continuousOn_iff_continuous_restrict.1 hg) ha'
      hb'
  ⟨x, x.2, hx⟩
theorem IsPreconnected.intermediate_value₂_eventually₁ {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (ha' : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ _
      (comap_coe_neBot_of_le_principal hl) _ _ hf hg ha' (he.comap _)
  exact ⟨b, b.prop, h⟩
theorem IsPreconnected.intermediate_value₂_eventually₂ {s : Set X} (hs : IsPreconnected s)
    {l₁ l₂ : Filter X} [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) :
    ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) _ _
      (comap_coe_neBot_of_le_principal hl₁) (comap_coe_neBot_of_le_principal hl₂) _ _ hf hg
      (he₁.comap _) (he₂.comap _)
  exact ⟨b, b.prop, h⟩
theorem IsPreconnected.intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s := fun _x hx =>
  hs.intermediate_value₂ ha hb hf continuousOn_const hx.1 hx.2
theorem IsPreconnected.intermediate_value_Ico {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ico (f a) v ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h.1 (ht.eventually_const_le h.2)
theorem IsPreconnected.intermediate_value_Ioc {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ioc v (f a) ⊆ f '' s := fun _ h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h.2
    (ht.eventually_le_const h.1)).imp fun _ h => h.imp_right Eq.symm
theorem IsPreconnected.intermediate_value_Ioo {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v₁ v₂ : α} (ht₁ : Tendsto f l₁ (𝓝 v₁)) (ht₂ : Tendsto f l₂ (𝓝 v₂)) :
    Ioo v₁ v₂ ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (ht₁.eventually_le_const h.1) (ht₂.eventually_const_le h.2)
theorem IsPreconnected.intermediate_value_Ici {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atTop) : Ici (f a) ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h (tendsto_atTop.1 ht y)
theorem IsPreconnected.intermediate_value_Iic {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atBot) : Iic (f a) ⊆ f '' s := fun y h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h (tendsto_atBot.1 ht y)).imp
    fun _ h => h.imp_right Eq.symm
theorem IsPreconnected.intermediate_value_Ioi {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ (𝓝 v)) (ht₂ : Tendsto f l₂ atTop) : Ioi v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (ht₁.eventually_le_const h) (ht₂.eventually_ge_atTop y)
theorem IsPreconnected.intermediate_value_Iio {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ (𝓝 v)) : Iio v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (ht₁.eventually_le_atBot y)
    (ht₂.eventually_const_le h)
theorem IsPreconnected.intermediate_value_Iii {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ atTop) : univ ⊆ f '' s := fun y _ =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (ht₁.eventually_le_atBot y)
    (ht₂.eventually_ge_atTop y)
theorem intermediate_value_univ [PreconnectedSpace X] (a b : X) {f : X → α} (hf : Continuous f) :
    Icc (f a) (f b) ⊆ range f := fun _ hx => intermediate_value_univ₂ hf continuous_const hx.1 hx.2
theorem mem_range_of_exists_le_of_exists_ge [PreconnectedSpace X] {c : α} {f : X → α}
    (hf : Continuous f) (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ range f :=
  let ⟨a, ha⟩ := h₁; let ⟨b, hb⟩ := h₂; intermediate_value_univ a b hf ⟨ha, hb⟩
theorem IsPreconnected.Icc_subset {s : Set α} (hs : IsPreconnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s := by
  simpa only [image_id] using hs.intermediate_value ha hb continuousOn_id
theorem IsPreconnected.ordConnected {s : Set α} (h : IsPreconnected s) : OrdConnected s :=
  ⟨fun _ hx _ hy => h.Icc_subset hx hy⟩
theorem IsConnected.Icc_subset {s : Set α} (hs : IsConnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s :=
  hs.2.Icc_subset ha hb
theorem IsPreconnected.eq_univ_of_unbounded {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : ¬BddAbove s) : s = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := not_bddBelow_iff.1 hb x
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
end
variable {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
theorem IsConnected.Ioo_csInf_csSup_subset {s : Set α} (hs : IsConnected s) (hb : BddBelow s)
    (ha : BddAbove s) : Ioo (sInf s) (sSup s) ⊆ s := fun _x hx =>
  let ⟨_y, ys, hy⟩ := (isGLB_lt_iff (isGLB_csInf hs.nonempty hb)).1 hx.1
  let ⟨_z, zs, hz⟩ := (lt_isLUB_iff (isLUB_csSup hs.nonempty ha)).1 hx.2
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩
theorem eq_Icc_csInf_csSup_of_connected_bdd_closed {s : Set α} (hc : IsConnected s)
    (hb : BddBelow s) (ha : BddAbove s) (hcl : IsClosed s) : s = Icc (sInf s) (sSup s) :=
  (subset_Icc_csInf_csSup hb ha).antisymm <|
    hc.Icc_subset (hcl.csInf_mem hc.nonempty hb) (hcl.csSup_mem hc.nonempty ha)
theorem IsPreconnected.Ioi_csInf_subset {s : Set α} (hs : IsPreconnected s) (hb : BddBelow s)
    (ha : ¬BddAbove s) : Ioi (sInf s) ⊆ s := fun x hx =>
  have sne : s.Nonempty := nonempty_of_not_bddAbove ha
  let ⟨_y, ys, hy⟩ : ∃ y ∈ s, y < x := (isGLB_lt_iff (isGLB_csInf sne hb)).1 hx
  let ⟨_z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩
theorem IsPreconnected.Iio_csSup_subset {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : BddAbove s) : Iio (sSup s) ⊆ s :=
  IsPreconnected.Ioi_csInf_subset (α := αᵒᵈ) hs ha hb
theorem IsPreconnected.mem_intervals {s : Set α} (hs : IsPreconnected s) :
    s ∈
      ({Icc (sInf s) (sSup s), Ico (sInf s) (sSup s), Ioc (sInf s) (sSup s), Ioo (sInf s) (sSup s),
          Ici (sInf s), Ioi (sInf s), Iic (sSup s), Iio (sSup s), univ, ∅} : Set (Set α)) := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · apply_rules [Or.inr, mem_singleton]
  have hs' : IsConnected s := ⟨hne, hs⟩
  by_cases hb : BddBelow s <;> by_cases ha : BddAbove s
  · refine mem_of_subset_of_mem ?_ <| mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
      (hs'.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
    simp only [insert_subset_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true,
      singleton_subset_iff, and_self]
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr ?_
    cases'
      mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_csInf_subset hb ha) fun x hx => csInf_le hb hx with
      hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 6 apply Or.inr
    cases' mem_Iic_Iio_of_subset_of_subset (hs.Iio_csSup_subset hb ha) fun x hx => le_csSup ha hx
      with hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 8 apply Or.inr
    exact Or.inl (hs.eq_univ_of_unbounded hb ha)
theorem setOf_isPreconnected_subset_of_ordered :
    { s : Set α | IsPreconnected s } ⊆
      (range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo)) ∪
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  intro s hs
  rcases hs.mem_intervals with (hs | hs | hs | hs | hs | hs | hs | hs | hs | hs) <;> rw [hs] <;>
    simp only [union_insert, union_singleton, mem_insert_iff, mem_union, mem_range, Prod.exists,
      uncurry_apply_pair, exists_apply_eq_apply, true_or, or_true, exists_apply_eq_apply2]
theorem IsClosed.mem_of_ge_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ico a b, (s ∩ Ioc x b).Nonempty) : b ∈ s := by
  let S := s ∩ Icc a b
  replace ha : a ∈ S := ⟨ha, left_mem_Icc.2 hab⟩
  have Sbd : BddAbove S := ⟨b, fun z hz => hz.2.2⟩
  let c := sSup (s ∩ Icc a b)
  have c_mem : c ∈ S := hs.csSup_mem ⟨_, ha⟩ Sbd
  have c_le : c ≤ b := csSup_le ⟨_, ha⟩ fun x hx => hx.2.2
  cases' eq_or_lt_of_le c_le with hc hc
  · exact hc ▸ c_mem.1
  exfalso
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩
  exact not_lt_of_le (le_csSup Sbd ⟨xs, le_trans (le_csSup Sbd ha) (le_of_lt cx), xb⟩) cx
theorem IsClosed.Icc_subset_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty) : Icc a b ⊆ s := by
  intro y hy
  have : IsClosed (s ∩ Icc a y) := by
    suffices s ∩ Icc a y = s ∩ Icc a b ∩ Icc a y by
      rw [this]
      exact IsClosed.inter hs isClosed_Icc
    rw [inter_assoc]
    congr
    exact (inter_eq_self_of_subset_right <| Icc_subset_Icc_right hy.2).symm
  exact
    IsClosed.mem_of_ge_of_forall_exists_gt this ha hy.1 fun x hx =>
      hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2
variable [DenselyOrdered α] {a b : α}
theorem IsClosed.Icc_subset_of_forall_mem_nhdsWithin {a b : α} {s : Set α}
    (hs : IsClosed (s ∩ Icc a b)) (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, s ∈ 𝓝[>] x) :
    Icc a b ⊆ s := by
  apply hs.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxs, hxab⟩ y hyxb
  have : s ∩ Ioc x y ∈ 𝓝[>] x :=
    inter_mem (hgt x ⟨hxs, hxab⟩) (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hyxb⟩)
  exact (nhdsWithin_Ioi_self_neBot' ⟨b, hxab.2⟩).nonempty_of_mem this
theorem isPreconnected_Icc_aux (x y : α) (s t : Set α) (hxy : x ≤ y) (hs : IsClosed s)
    (ht : IsClosed t) (hab : Icc a b ⊆ s ∪ t) (hx : x ∈ Icc a b ∩ s) (hy : y ∈ Icc a b ∩ t) :
    (Icc a b ∩ (s ∩ t)).Nonempty := by
  have xyab : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.1 hy.1.2
  by_contra hst
  suffices Icc x y ⊆ s from
    hst ⟨y, xyab <| right_mem_Icc.2 hxy, this <| right_mem_Icc.2 hxy, hy.2⟩
  apply (IsClosed.inter hs isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin hx.2
  rintro z ⟨zs, hz⟩
  have zt : z ∈ tᶜ := fun zt => hst ⟨z, xyab <| Ico_subset_Icc_self hz, zs, zt⟩
  have : tᶜ ∩ Ioc z y ∈ 𝓝[>] z := by
    rw [← nhdsWithin_Ioc_eq_nhdsWithin_Ioi hz.2]
    exact mem_nhdsWithin.2 ⟨tᶜ, ht.isOpen_compl, zt, Subset.rfl⟩
  apply mem_of_superset this
  have : Ioc z y ⊆ s ∪ t := fun w hw => hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩)
  exact fun w ⟨wt, wzy⟩ => (this wzy).elim id fun h => (wt h).elim
theorem isPreconnected_Icc : IsPreconnected (Icc a b) :=
  isPreconnected_closed_iff.2
    (by
      rintro s t hs ht hab ⟨x, hx⟩ ⟨y, hy⟩
      rcases le_total x y with h | h
      · exact isPreconnected_Icc_aux x y s t h hs ht hab hx hy
      · rw [inter_comm s t]
        rw [union_comm s t] at hab
        exact isPreconnected_Icc_aux y x t s h ht hs hab hy hx)
theorem isPreconnected_uIcc : IsPreconnected ([[a, b]]) :=
  isPreconnected_Icc
theorem Set.OrdConnected.isPreconnected {s : Set α} (h : s.OrdConnected) : IsPreconnected s :=
  isPreconnected_of_forall_pair fun x hx y hy =>
    ⟨[[x, y]], h.uIcc_subset hx hy, left_mem_uIcc, right_mem_uIcc, isPreconnected_uIcc⟩
theorem isPreconnected_iff_ordConnected {s : Set α} : IsPreconnected s ↔ OrdConnected s :=
  ⟨IsPreconnected.ordConnected, Set.OrdConnected.isPreconnected⟩
theorem isPreconnected_Ici : IsPreconnected (Ici a) :=
  ordConnected_Ici.isPreconnected
theorem isPreconnected_Iic : IsPreconnected (Iic a) :=
  ordConnected_Iic.isPreconnected
theorem isPreconnected_Iio : IsPreconnected (Iio a) :=
  ordConnected_Iio.isPreconnected
theorem isPreconnected_Ioi : IsPreconnected (Ioi a) :=
  ordConnected_Ioi.isPreconnected
theorem isPreconnected_Ioo : IsPreconnected (Ioo a b) :=
  ordConnected_Ioo.isPreconnected
theorem isPreconnected_Ioc : IsPreconnected (Ioc a b) :=
  ordConnected_Ioc.isPreconnected
theorem isPreconnected_Ico : IsPreconnected (Ico a b) :=
  ordConnected_Ico.isPreconnected
theorem isConnected_Ici : IsConnected (Ici a) :=
  ⟨nonempty_Ici, isPreconnected_Ici⟩
theorem isConnected_Iic : IsConnected (Iic a) :=
  ⟨nonempty_Iic, isPreconnected_Iic⟩
theorem isConnected_Ioi [NoMaxOrder α] : IsConnected (Ioi a) :=
  ⟨nonempty_Ioi, isPreconnected_Ioi⟩
theorem isConnected_Iio [NoMinOrder α] : IsConnected (Iio a) :=
  ⟨nonempty_Iio, isPreconnected_Iio⟩
theorem isConnected_Icc (h : a ≤ b) : IsConnected (Icc a b) :=
  ⟨nonempty_Icc.2 h, isPreconnected_Icc⟩
theorem isConnected_Ioo (h : a < b) : IsConnected (Ioo a b) :=
  ⟨nonempty_Ioo.2 h, isPreconnected_Ioo⟩
theorem isConnected_Ioc (h : a < b) : IsConnected (Ioc a b) :=
  ⟨nonempty_Ioc.2 h, isPreconnected_Ioc⟩
theorem isConnected_Ico (h : a < b) : IsConnected (Ico a b) :=
  ⟨nonempty_Ico.2 h, isPreconnected_Ico⟩
instance (priority := 100) ordered_connected_space : PreconnectedSpace α :=
  ⟨ordConnected_univ.isPreconnected⟩
theorem setOf_isPreconnected_eq_of_ordered :
    { s : Set α | IsPreconnected s } =
      range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  refine Subset.antisymm setOf_isPreconnected_subset_of_ordered ?_
  simp only [subset_def, forall_mem_range, uncurry, or_imp, forall_and, mem_union,
    mem_setOf_eq, insert_eq, mem_singleton_iff, forall_eq, forall_true_iff, and_true,
    isPreconnected_Icc, isPreconnected_Ico, isPreconnected_Ioc, isPreconnected_Ioo,
    isPreconnected_Ioi, isPreconnected_Iio, isPreconnected_Ici, isPreconnected_Iic,
    isPreconnected_univ, isPreconnected_empty]
lemma isTotallyDisconnected_iff_lt {s : Set α} :
    IsTotallyDisconnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x < y → ∃ z ∉ s, z ∈ Ioo x y := by
  simp only [IsTotallyDisconnected, isPreconnected_iff_ordConnected, ← not_nontrivial_iff,
    nontrivial_iff_exists_lt, not_exists, not_and]
  refine ⟨fun h x hx y hy hxy ↦ ?_, fun h t hts ht x hx y hy hxy ↦ ?_⟩
  · simp_rw [← not_ordConnected_inter_Icc_iff hx hy]
    exact fun hs ↦ h _ inter_subset_left hs _ ⟨hx, le_rfl, hxy.le⟩ _ ⟨hy, hxy.le, le_rfl⟩ hxy
  · obtain ⟨z, h1z, h2z⟩ := h x (hts hx) y (hts hy) hxy
    exact h1z <| hts <| ht.1 hx hy ⟨h2z.1.le, h2z.2.le⟩
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf
theorem intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f b) (f a) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf
theorem intermediate_value_uIcc {a b : α} {f : α → δ} (hf : ContinuousOn f [[a, b]]) :
    [[f a, f b]] ⊆ f '' uIcc a b := by
  cases le_total (f a) (f b) <;> simp [*, isPreconnected_uIcc.intermediate_value]
theorem exists_mem_uIcc_isFixedPt {a b : α} {f : α → α} (hf : ContinuousOn f (uIcc a b))
    (ha : a ≤ f a) (hb : f b ≤ b) : ∃ c ∈ [[a, b]], IsFixedPt f c :=
  isPreconnected_uIcc.intermediate_value₂ right_mem_uIcc left_mem_uIcc hf continuousOn_id hb ha
theorem exists_mem_Icc_isFixedPt {a b : α} {f : α → α} (hf : ContinuousOn f (Icc a b))
    (hle : a ≤ b) (ha : a ≤ f a) (hb : f b ≤ b) : ∃ c ∈ Icc a b, IsFixedPt f c :=
  isPreconnected_Icc.intermediate_value₂
    (right_mem_Icc.2 hle) (left_mem_Icc.2 hle) hf continuousOn_id hb ha
theorem exists_mem_Icc_isFixedPt_of_mapsTo {a b : α} {f : α → α} (hf : ContinuousOn f (Icc a b))
    (hle : a ≤ b) (hmaps : MapsTo f (Icc a b) (Icc a b)) : ∃ c ∈ Icc a b, IsFixedPt f c :=
  exists_mem_Icc_isFixedPt hf hle (hmaps <| left_mem_Icc.2 hle).1 (hmaps <| right_mem_Icc.2 hle).2
theorem intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ico (f a) (f b) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_le (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
theorem intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioc (f b) (f a) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_le (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
theorem intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioc (f a) (f b) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_le_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
theorem intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ico (f b) (f a) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_le_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
theorem intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioo (f a) (f b) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (left_nhdsWithin_Ioo_neBot hlt) (right_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
theorem intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioo (f b) (f a) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (right_nhdsWithin_Ioo_neBot hlt) (left_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
theorem ContinuousOn.surjOn_Icc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (Icc (f a) (f b)) :=
  hs.isPreconnected.intermediate_value ha hb hf
theorem ContinuousOn.surjOn_uIcc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    SurjOn f s (uIcc (f a) (f b)) := by
  rcases le_total (f a) (f b) with hab | hab <;> simp [hf.surjOn_Icc, *]
theorem Continuous.surjective {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atTop atTop)
    (h_bot : Tendsto f atBot atBot) : Function.Surjective f := fun p =>
  mem_range_of_exists_le_of_exists_ge hf (h_bot.eventually (eventually_le_atBot p)).exists
    (h_top.eventually (eventually_ge_atTop p)).exists
theorem Continuous.surjective' {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atBot atTop)
    (h_bot : Tendsto f atTop atBot) : Function.Surjective f :=
  Continuous.surjective (α := αᵒᵈ) hf h_top h_bot
theorem ContinuousOn.surjOn_of_tendsto {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atBot)
    (htop : Tendsto (fun x : s => f x) atTop atTop) : SurjOn f s univ :=
  haveI := Classical.inhabited_of_nonempty hs.to_subtype
  surjOn_iff_surjective.2 <| hf.restrict.surjective htop hbot
theorem ContinuousOn.surjOn_of_tendsto' {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atTop)
    (htop : Tendsto (fun x : s => f x) atTop atBot) : SurjOn f s univ :=
  ContinuousOn.surjOn_of_tendsto (δ := δᵒᵈ) hs hf hbot htop
theorem Continuous.strictMono_of_inj_boundedOrder [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf : f ⊥ ≤ f ⊤) (hf_i : Injective f) : StrictMono f := by
  intro a b hab
  by_contra! h
  have H : f b < f a := lt_of_le_of_ne h <| hf_i.ne hab.ne'
  by_cases ha : f a ≤ f ⊥
  · obtain ⟨u, hu⟩ := intermediate_value_Ioc le_top hf_c.continuousOn ⟨H.trans_le ha, hf⟩
    have : u = ⊥ := hf_i hu.2
    aesop
  · by_cases hb : f ⊥ < f b
    · obtain ⟨u, hu⟩ := intermediate_value_Ioo bot_le hf_c.continuousOn ⟨hb, H⟩
      rw [hf_i hu.2] at hu
      exact (hab.trans hu.1.2).false
    · push_neg at ha hb
      replace hb : f b < f ⊥ := lt_of_le_of_ne hb <| hf_i.ne (lt_of_lt_of_le' hab bot_le).ne'
      obtain ⟨u, hu⟩ := intermediate_value_Ioo' hab.le hf_c.continuousOn ⟨hb, ha⟩
      have : u = ⊥ := hf_i hu.2
      aesop
theorem Continuous.strictAnti_of_inj_boundedOrder [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf : f ⊤ ≤ f ⊥) (hf_i : Injective f) : StrictAnti f :=
  hf_c.strictMono_of_inj_boundedOrder (δ := δᵒᵈ) hf hf_i
theorem Continuous.strictMono_of_inj_boundedOrder' [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) : StrictMono f ∨ StrictAnti f :=
  (le_total (f ⊥) (f ⊤)).imp
    (hf_c.strictMono_of_inj_boundedOrder · hf_i)
    (hf_c.strictAnti_of_inj_boundedOrder · hf_i)
theorem Continuous.strictMonoOn_of_inj_rigidity {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) {a b : α} (hab : a < b)
    (hf_mono : StrictMonoOn f (Icc a b)) : StrictMono f := by
  intro x y hxy
  let s := min a x
  let t := max b y
  have hsa : s ≤ a := min_le_left a x
  have hbt : b ≤ t := le_max_left b y
  have hf_mono_st : StrictMonoOn f (Icc s t) ∨ StrictAntiOn f (Icc s t) := by
    have : Fact (s ≤ t) := ⟨hsa.trans <| hbt.trans' hab.le⟩
    have := Continuous.strictMono_of_inj_boundedOrder' (f := Set.restrict (Icc s t) f)
      hf_c.continuousOn.restrict hf_i.injOn.injective
    exact this.imp strictMono_restrict.mp strictAntiOn_iff_strictAnti.mpr
  have (h : StrictAntiOn f (Icc s t)) : False := by
    have : Icc a b ⊆ Icc s t := Icc_subset_Icc hsa hbt
    replace : StrictAntiOn f (Icc a b) := StrictAntiOn.mono h this
    replace : IsAntichain (· ≤ ·) (Icc a b) :=
      IsAntichain.of_strictMonoOn_antitoneOn hf_mono this.antitoneOn
    exact this.not_lt (left_mem_Icc.mpr (le_of_lt hab)) (right_mem_Icc.mpr (le_of_lt hab)) hab
  replace hf_mono_st : StrictMonoOn f (Icc s t) := hf_mono_st.resolve_right this
  have hsx : s ≤ x := min_le_right a x
  have hyt : y ≤ t := le_max_right b y
  replace : Icc x y ⊆ Icc s t := Icc_subset_Icc hsx hyt
  replace : StrictMonoOn f (Icc x y) := StrictMonoOn.mono hf_mono_st this
  exact this (left_mem_Icc.mpr (le_of_lt hxy)) (right_mem_Icc.mpr (le_of_lt hxy)) hxy
theorem ContinuousOn.strictMonoOn_of_injOn_Icc {a b : α} {f : α → δ}
    (hab : a ≤ b) (hfab : f a ≤ f b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) := by
  have : Fact (a ≤ b) := ⟨hab⟩
  refine StrictMono.of_restrict ?_
  set g : Icc a b → δ := Set.restrict (Icc a b) f
  have hgab : g ⊥ ≤ g ⊤ := by aesop
  exact Continuous.strictMono_of_inj_boundedOrder (f := g) hf_c.restrict hgab hf_i.injective
theorem ContinuousOn.strictAntiOn_of_injOn_Icc {a b : α} {f : α → δ}
    (hab : a ≤ b) (hfab : f b ≤ f a)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictAntiOn f (Icc a b) := ContinuousOn.strictMonoOn_of_injOn_Icc (δ := δᵒᵈ) hab hfab hf_c hf_i
theorem ContinuousOn.strictMonoOn_of_injOn_Icc' {a b : α} {f : α → δ} (hab : a ≤ b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b) :=
  (le_total (f a) (f b)).imp
    (ContinuousOn.strictMonoOn_of_injOn_Icc hab · hf_c hf_i)
    (ContinuousOn.strictAntiOn_of_injOn_Icc hab · hf_c hf_i)
theorem Continuous.strictMono_of_inj {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) : StrictMono f ∨ StrictAnti f := by
  have H {c d : α} (hcd : c < d) : StrictMono f ∨ StrictAnti f :=
    (hf_c.continuousOn.strictMonoOn_of_injOn_Icc' hcd.le hf_i.injOn).imp
      (hf_c.strictMonoOn_of_inj_rigidity hf_i hcd)
      (hf_c.strictMonoOn_of_inj_rigidity (δ := δᵒᵈ) hf_i hcd)
  by_cases hn : Nonempty α
  · let a : α := Classical.choice ‹_›
    by_cases h : ∃ b : α, a ≠ b
    · choose b hb using h
      by_cases hab : a < b
      · exact H hab
      · push_neg at hab
        have : b < a := by exact Ne.lt_of_le (id (Ne.symm hb)) hab
        exact H this
    · push_neg at h
      haveI : Subsingleton α := ⟨fun c d => Trans.trans (h c).symm (h d)⟩
      exact Or.inl <| Subsingleton.strictMono f
  · aesop
theorem ContinuousOn.strictMonoOn_of_injOn_Ioo {a b : α} {f : α → δ} (hab : a < b)
    (hf_c : ContinuousOn f (Ioo a b)) (hf_i : InjOn f (Ioo a b)) :
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b) := by
  haveI : Inhabited (Ioo a b) := Classical.inhabited_of_nonempty (nonempty_Ioo_subtype hab)
  let g : Ioo a b → δ := Set.restrict (Ioo a b) f
  have : StrictMono g ∨ StrictAnti g :=
    Continuous.strictMono_of_inj hf_c.restrict hf_i.injective
  exact this.imp strictMono_restrict.mp strictAntiOn_iff_strictAnti.mpr