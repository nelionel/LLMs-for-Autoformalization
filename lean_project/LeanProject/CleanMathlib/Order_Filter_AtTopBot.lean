import Mathlib.Data.Finset.Preimage
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.Bases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.Interval.Set.OrderIso
variable {ι ι' α β γ : Type*}
open Set
namespace Filter
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
def atBot [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Iic a)
theorem mem_atTop [Preorder α] (a : α) : { b : α | a ≤ b } ∈ @atTop α _ :=
  mem_iInf_of_mem a <| Subset.refl _
theorem Ici_mem_atTop [Preorder α] (a : α) : Ici a ∈ (atTop : Filter α) :=
  mem_atTop a
theorem Ioi_mem_atTop [Preorder α] [NoMaxOrder α] (x : α) : Ioi x ∈ (atTop : Filter α) :=
  let ⟨z, hz⟩ := exists_gt x
  mem_of_superset (mem_atTop z) fun _ h => lt_of_lt_of_le hz h
theorem mem_atBot [Preorder α] (a : α) : { b : α | b ≤ a } ∈ @atBot α _ :=
  mem_iInf_of_mem a <| Subset.refl _
theorem Iic_mem_atBot [Preorder α] (a : α) : Iic a ∈ (atBot : Filter α) :=
  mem_atBot a
theorem Iio_mem_atBot [Preorder α] [NoMinOrder α] (x : α) : Iio x ∈ (atBot : Filter α) :=
  let ⟨z, hz⟩ := exists_lt x
  mem_of_superset (mem_atBot z) fun _ h => lt_of_le_of_lt h hz
theorem disjoint_atBot_principal_Ioi [Preorder α] (x : α) : Disjoint atBot (𝓟 (Ioi x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl) (Iic_mem_atBot x) (mem_principal_self _)
theorem disjoint_atTop_principal_Iio [Preorder α] (x : α) : Disjoint atTop (𝓟 (Iio x)) :=
  @disjoint_atBot_principal_Ioi αᵒᵈ _ _
theorem disjoint_atTop_principal_Iic [Preorder α] [NoMaxOrder α] (x : α) :
    Disjoint atTop (𝓟 (Iic x)) :=
  disjoint_of_disjoint_of_mem (Iic_disjoint_Ioi le_rfl).symm (Ioi_mem_atTop x)
    (mem_principal_self _)
theorem disjoint_atBot_principal_Ici [Preorder α] [NoMinOrder α] (x : α) :
    Disjoint atBot (𝓟 (Ici x)) :=
  @disjoint_atTop_principal_Iic αᵒᵈ _ _ _
theorem disjoint_pure_atTop [Preorder α] [NoMaxOrder α] (x : α) : Disjoint (pure x) atTop :=
  Disjoint.symm <| (disjoint_atTop_principal_Iic x).mono_right <| le_principal_iff.2 <|
    mem_pure.2 right_mem_Iic
theorem disjoint_pure_atBot [Preorder α] [NoMinOrder α] (x : α) : Disjoint (pure x) atBot :=
  @disjoint_pure_atTop αᵒᵈ _ _ _
theorem not_tendsto_const_atTop [Preorder α] [NoMaxOrder α] (x : α) (l : Filter β) [l.NeBot] :
    ¬Tendsto (fun _ => x) l atTop :=
  tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)
theorem not_tendsto_const_atBot [Preorder α] [NoMinOrder α] (x : α) (l : Filter β) [l.NeBot] :
    ¬Tendsto (fun _ => x) l atBot :=
  tendsto_const_pure.not_tendsto (disjoint_pure_atBot x)
theorem disjoint_atBot_atTop [PartialOrder α] [Nontrivial α] :
    Disjoint (atBot : Filter α) atTop := by
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  by_cases hle : x ≤ y
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot x) (Ici_mem_atTop y)
    exact Iic_disjoint_Ici.2 (hle.lt_of_ne hne).not_le
  · refine disjoint_of_disjoint_of_mem ?_ (Iic_mem_atBot y) (Ici_mem_atTop x)
    exact Iic_disjoint_Ici.2 hle
theorem disjoint_atTop_atBot [PartialOrder α] [Nontrivial α] : Disjoint (atTop : Filter α) atBot :=
  disjoint_atBot_atTop.symm
theorem eventually_ge_atTop [Preorder α] (a : α) : ∀ᶠ x in atTop, a ≤ x :=
  mem_atTop a
theorem eventually_le_atBot [Preorder α] (a : α) : ∀ᶠ x in atBot, x ≤ a :=
  mem_atBot a
theorem eventually_gt_atTop [Preorder α] [NoMaxOrder α] (a : α) : ∀ᶠ x in atTop, a < x :=
  Ioi_mem_atTop a
theorem eventually_ne_atTop [Preorder α] [NoMaxOrder α] (a : α) : ∀ᶠ x in atTop, x ≠ a :=
  (eventually_gt_atTop a).mono fun _ => ne_of_gt
protected theorem Tendsto.eventually_gt_atTop [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c < f x :=
  hf.eventually (eventually_gt_atTop c)
protected theorem Tendsto.eventually_ge_atTop [Preorder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c ≤ f x :=
  hf.eventually (eventually_ge_atTop c)
protected theorem Tendsto.eventually_ne_atTop [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, f x ≠ c :=
  hf.eventually (eventually_ne_atTop c)
protected theorem Tendsto.eventually_ne_atTop' [Preorder β] [NoMaxOrder β] {f : α → β}
    {l : Filter α} (hf : Tendsto f l atTop) (c : α) : ∀ᶠ x in l, x ≠ c :=
  (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f
theorem eventually_lt_atBot [Preorder α] [NoMinOrder α] (a : α) : ∀ᶠ x in atBot, x < a :=
  Iio_mem_atBot a
theorem eventually_ne_atBot [Preorder α] [NoMinOrder α] (a : α) : ∀ᶠ x in atBot, x ≠ a :=
  (eventually_lt_atBot a).mono fun _ => ne_of_lt
protected theorem Tendsto.eventually_lt_atBot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atBot) (c : β) : ∀ᶠ x in l, f x < c :=
  hf.eventually (eventually_lt_atBot c)
protected theorem Tendsto.eventually_le_atBot [Preorder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atBot) (c : β) : ∀ᶠ x in l, f x ≤ c :=
  hf.eventually (eventually_le_atBot c)
protected theorem Tendsto.eventually_ne_atBot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atBot) (c : β) : ∀ᶠ x in l, f x ≠ c :=
  hf.eventually (eventually_ne_atBot c)
theorem eventually_forall_ge_atTop [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atTop, ∀ y, x ≤ y → p y) ↔ ∀ᶠ x in atTop, p x := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ hx x le_rfl, fun h ↦ ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x ↦ Ici x.1) (fun _ ↦ Subset.rfl) fun x hx y hy ↦ ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz ↦ le_trans (hx ⟨z, hz⟩) hy
theorem eventually_forall_le_atBot [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atBot, ∀ y, y ≤ x → p y) ↔ ∀ᶠ x in atBot, p x :=
  eventually_forall_ge_atTop (α := αᵒᵈ)
theorem Tendsto.eventually_forall_ge_atTop [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atTop) (h_evtl : ∀ᶠ x in atTop, p x) :
    ∀ᶠ x in l, ∀ y, f x ≤ y → p y := by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap
theorem Tendsto.eventually_forall_le_atBot [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atBot) (h_evtl : ∀ᶠ x in atBot, p x) :
    ∀ᶠ x in l, ∀ y, y ≤ f x → p y := by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap
instance (priority := 200) atTop.isCountablyGenerated [Preorder α] [Countable α] :
    (atTop : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _
instance (priority := 200) atBot.isCountablyGenerated [Preorder α] [Countable α] :
    (atBot : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _
instance _root_.OrderDual.instIsCountablyGeneratedAtTop [Preorder α]
    [IsCountablyGenerated (atBot : Filter α)] : IsCountablyGenerated (atTop : Filter αᵒᵈ) := ‹_›
instance _root_.OrderDual.instIsCountablyGeneratedAtBot [Preorder α]
    [IsCountablyGenerated (atTop : Filter α)] : IsCountablyGenerated (atBot : Filter αᵒᵈ) := ‹_›
theorem _root_.IsTop.atTop_eq [Preorder α] {a : α} (ha : IsTop a) : atTop = 𝓟 (Ici a) :=
  (iInf_le _ _).antisymm <| le_iInf fun b ↦ principal_mono.2 <| Ici_subset_Ici.2 <| ha b
theorem _root_.IsBot.atBot_eq [Preorder α] {a : α} (ha : IsBot a) : atBot = 𝓟 (Iic a) :=
  ha.toDual.atTop_eq
theorem OrderTop.atTop_eq (α) [PartialOrder α] [OrderTop α] : (atTop : Filter α) = pure ⊤ := by
  rw [isTop_top.atTop_eq, Ici_top, principal_singleton]
theorem OrderBot.atBot_eq (α) [PartialOrder α] [OrderBot α] : (atBot : Filter α) = pure ⊥ :=
  @OrderTop.atTop_eq αᵒᵈ _ _
@[nontriviality]
theorem Subsingleton.atTop_eq (α) [Subsingleton α] [Preorder α] : (atTop : Filter α) = ⊤ := by
  refine top_unique fun s hs x => ?_
  rw [atTop, ciInf_subsingleton x, mem_principal] at hs
  exact hs left_mem_Ici
@[nontriviality]
theorem Subsingleton.atBot_eq (α) [Subsingleton α] [Preorder α] : (atBot : Filter α) = ⊤ :=
  @Subsingleton.atTop_eq αᵒᵈ _ _
theorem tendsto_atTop_pure [PartialOrder α] [OrderTop α] (f : α → β) :
    Tendsto f atTop (pure <| f ⊤) :=
  (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _
theorem tendsto_atBot_pure [PartialOrder α] [OrderBot α] (f : α → β) :
    Tendsto f atBot (pure <| f ⊥) :=
  @tendsto_atTop_pure αᵒᵈ _ _ _ _
theorem atTop_eq_generate_Ici [Preorder α] : atTop = generate (range (Ici (α := α))) := by
  simp only [generate_eq_biInf, atTop, iInf_range]
theorem Frequently.forall_exists_of_atTop [Preorder α] {p : α → Prop}
    (h : ∃ᶠ x in atTop, p x) (a : α) : ∃ b ≥ a, p b := by
  rw [Filter.Frequently] at h
  contrapose! h
  exact (eventually_ge_atTop a).mono h
theorem Frequently.forall_exists_of_atBot [Preorder α] {p : α → Prop}
    (h : ∃ᶠ x in atBot, p x) (a : α) : ∃ b ≤ a, p b :=
  Frequently.forall_exists_of_atTop (α := αᵒᵈ) h _
section IsDirected
variable [Preorder α] [IsDirected α (· ≤ ·)] {p : α → Prop}
theorem hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici :=
  .iInf_principal fun _ _ ↦ Ici_subset_Ici.2
theorem atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici :=
  hasAntitoneBasis_atTop.1
lemma atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _ => True) Ioi :=
  atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩
lemma atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩
theorem atTop_basis' (a : α) : atTop.HasBasis (a ≤ ·) Ici := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩
variable [Nonempty α]
@[instance]
lemma atTop_neBot : NeBot (atTop : Filter α) := atTop_basis.neBot_iff.2 fun _ => nonempty_Ici
theorem atTop_neBot_iff {α : Type*} [Preorder α] :
    (atTop : Filter α).NeBot ↔ Nonempty α ∧ IsDirected α (· ≤ ·) := by
  refine ⟨fun h ↦ ⟨nonempty_of_neBot atTop, ⟨fun x y ↦ ?_⟩⟩, fun ⟨h₁, h₂⟩ ↦ atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists
theorem atBot_neBot_iff {α : Type*} [Preorder α] :
    (atBot : Filter α).NeBot ↔ Nonempty α ∧ IsDirected α (· ≥ ·) :=
  atTop_neBot_iff (α := αᵒᵈ)
@[simp] lemma mem_atTop_sets {s : Set α} : s ∈ (atTop : Filter α) ↔ ∃ a : α, ∀ b ≥ a, b ∈ s :=
  atTop_basis.mem_iff.trans <| exists_congr fun _ => iff_of_eq (true_and _)
@[simp] lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b := mem_atTop_sets
theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b :=
  atTop_basis.frequently_iff.trans <| by simp
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop
lemma exists_eventually_atTop {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atTop, r a b) ↔ ∀ᶠ a₀ in atTop, ∃ b, ∀ a ≥ a₀, r a b := by
  simp_rw [eventually_atTop, ← exists_swap (α := α)]
  exact exists_congr fun a ↦ .symm <| forall_ge_iff <| Monotone.exists fun _ _ _ hb H n hn ↦
    H n (hb.trans hn)
theorem map_atTop_eq {f : α → β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a ≤ a' }) :=
  (atTop_basis.map f).eq_iInf
theorem frequently_atTop' [NoMaxOrder α] : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b > a, p b :=
  atTop_basis_Ioi.frequently_iff.trans <| by simp
lemma atTop_countable_basis [Countable α] :
    HasCountableBasis (atTop : Filter α) (fun _ => True) Ici :=
  { atTop_basis with countable := to_countable _ }
end IsDirected
section IsCodirected
variable [Preorder α] [IsDirected α (· ≥ ·)] {p : α → Prop}
lemma atBot_basis_Iio [Nonempty α] [NoMinOrder α] : (@atBot α _).HasBasis (fun _ => True) Iio :=
  atTop_basis_Ioi (α := αᵒᵈ)
lemma atBot_basis_Iio' [NoMinOrder α] (a : α) : atBot.HasBasis (· < a) Iio :=
  atTop_basis_Ioi' (α := αᵒᵈ) a
lemma atBot_basis' (a : α) : (@atBot α _).HasBasis (fun x => x ≤ a) Iic := atTop_basis' (α := αᵒᵈ) _
variable [Nonempty α]
lemma atBot_basis : (@atBot α _).HasBasis (fun _ => True) Iic := atTop_basis (α := αᵒᵈ)
@[instance] lemma atBot_neBot : NeBot (atBot : Filter α) := atTop_neBot (α := αᵒᵈ)
@[simp] lemma mem_atBot_sets {s : Set α} : s ∈ (atBot : Filter α) ↔ ∃ a : α, ∀ b ≤ a, b ∈ s :=
  mem_atTop_sets (α := αᵒᵈ)
@[simp] lemma eventually_atBot : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ b ≤ a, p b := mem_atBot_sets
theorem frequently_atBot : (∃ᶠ x in atBot, p x) ↔ ∀ a, ∃ b ≤ a, p b := frequently_atTop (α := αᵒᵈ)
alias ⟨Eventually.exists_forall_of_atBot, _⟩ := eventually_atBot
lemma exists_eventually_atBot {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atBot, r a b) ↔ ∀ᶠ a₀ in atBot, ∃ b, ∀ a ≤ a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)
theorem map_atBot_eq {f : α → β} : atBot.map f = ⨅ a, 𝓟 (f '' { a' | a' ≤ a }) :=
  map_atTop_eq (α := αᵒᵈ)
theorem frequently_atBot' [NoMinOrder α] : (∃ᶠ x in atBot, p x) ↔ ∀ a, ∃ b < a, p b :=
  frequently_atTop' (α := αᵒᵈ)
lemma atBot_countable_basis [Countable α] :
    HasCountableBasis (atBot : Filter α) (fun _ => True) Iic :=
  { atBot_basis with countable := to_countable _ }
end IsCodirected
theorem tendsto_atTop [Preorder β] {m : α → β} {f : Filter α} :
    Tendsto m f atTop ↔ ∀ b, ∀ᶠ a in f, b ≤ m a := by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]
theorem tendsto_atBot [Preorder β] {m : α → β} {f : Filter α} :
    Tendsto m f atBot ↔ ∀ b, ∀ᶠ a in f, m a ≤ b :=
  @tendsto_atTop α βᵒᵈ _ m f
theorem tendsto_atTop_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄ (h : f₁ ≤ᶠ[l] f₂)
    (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l atTop :=
  tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans
theorem tendsto_atBot_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄ (h : f₁ ≤ᶠ[l] f₂) :
    Tendsto f₂ l atBot → Tendsto f₁ l atBot :=
  @tendsto_atTop_mono' _ βᵒᵈ _ _ _ _ h
theorem tendsto_atTop_mono [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ n, f n ≤ g n) :
    Tendsto f l atTop → Tendsto g l atTop :=
  tendsto_atTop_mono' l <| Eventually.of_forall h
theorem tendsto_atBot_mono [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ n, f n ≤ g n) :
    Tendsto g l atBot → Tendsto f l atBot :=
  @tendsto_atTop_mono _ βᵒᵈ _ _ _ _ h
lemma atTop_eq_generate_of_forall_exists_le [LinearOrder α] {s : Set α} (hs : ∀ x, ∃ y ∈ s, x ≤ y) :
    (atTop : Filter α) = generate (Ici '' s) := by
  rw [atTop_eq_generate_Ici]
  apply le_antisymm
  · rw [le_generate_iff]
    rintro - ⟨y, -, rfl⟩
    exact mem_generate_of_mem ⟨y, rfl⟩
  · rw [le_generate_iff]
    rintro - ⟨x, -, -, rfl⟩
    rcases hs x with ⟨y, ys, hy⟩
    have A : Ici y ∈ generate (Ici '' s) := mem_generate_of_mem (mem_image_of_mem _ ys)
    have B : Ici y ⊆ Ici x := Ici_subset_Ici.2 hy
    exact sets_of_superset (generate (Ici '' s)) A B
lemma atTop_eq_generate_of_not_bddAbove [LinearOrder α] {s : Set α} (hs : ¬ BddAbove s) :
    (atTop : Filter α) = generate (Ici '' s) := by
  refine atTop_eq_generate_of_forall_exists_le fun x ↦ ?_
  obtain ⟨y, hy, hy'⟩ := not_bddAbove_iff.mp hs x
  exact ⟨y, hy, hy'.le⟩
end Filter
namespace OrderIso
open Filter
variable [Preorder α] [Preorder β]
@[simp]
theorem comap_atTop (e : α ≃o β) : comap e atTop = atTop := by
  simp [atTop, ← e.surjective.iInf_comp]
@[simp]
theorem comap_atBot (e : α ≃o β) : comap e atBot = atBot :=
  e.dual.comap_atTop
@[simp]
theorem map_atTop (e : α ≃o β) : map (e : α → β) atTop = atTop := by
  rw [← e.comap_atTop, map_comap_of_surjective e.surjective]
@[simp]
theorem map_atBot (e : α ≃o β) : map (e : α → β) atBot = atBot :=
  e.dual.map_atTop
theorem tendsto_atTop (e : α ≃o β) : Tendsto e atTop atTop :=
  e.map_atTop.le
theorem tendsto_atBot (e : α ≃o β) : Tendsto e atBot atBot :=
  e.map_atBot.le
@[simp]
theorem tendsto_atTop_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← e.comap_atTop, tendsto_comap_iff, Function.comp_def]
@[simp]
theorem tendsto_atBot_iff {l : Filter γ} {f : γ → α} (e : α ≃o β) :
    Tendsto (fun x => e (f x)) l atBot ↔ Tendsto f l atBot :=
  e.dual.tendsto_atTop_iff
end OrderIso
namespace Filter
theorem extraction_of_frequently_atTop' {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  choose u hu hu' using h
  refine ⟨fun n => u^[n + 1] 0, strictMono_nat_of_lt_succ fun n => ?_, fun n => ?_⟩
  · exact Trans.trans (hu _) (Function.iterate_succ_apply' _ _ _).symm
  · simpa only [Function.iterate_succ_apply'] using hu' _
theorem extraction_of_frequently_atTop {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  rw [frequently_atTop'] at h
  exact extraction_of_frequently_atTop' h
theorem extraction_of_eventually_atTop {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) :=
  extraction_of_frequently_atTop h.frequently
theorem extraction_forall_of_frequently {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) := by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : ℕ → ℕ)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']
theorem extraction_forall_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_frequently fun n => (h n).frequently
theorem extraction_forall_of_eventually' {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ N, ∀ k ≥ N, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_eventually (by simp [eventually_atTop, h])
theorem Eventually.atTop_of_arithmetic {p : ℕ → Prop} {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ k < n, ∀ᶠ a in atTop, p (n * a + k)) : ∀ᶠ a in atTop, p a := by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [ge_iff_le, Nat.le_div_iff_mul_le hn.bot_lt, mul_comm]
  exact (Finset.le_sup (f := (n * N ·)) (Finset.mem_range.2 hlt)).trans hb
section IsDirected
variable [Preorder α] [IsDirected α (· ≤ ·)] {F : Filter β} {u : α → β}
theorem inf_map_atTop_neBot_iff [Nonempty α] :
    NeBot (F ⊓ map u atTop) ↔ ∀ U ∈ F, ∀ N, ∃ n ≥ N, u n ∈ U := by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl
variable [Preorder β]
lemma exists_le_of_tendsto_atTop (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a' ≥ a, b ≤ u a' := by
  have : Nonempty α := ⟨a⟩
  have : ∀ᶠ x in atTop, a ≤ x ∧ b ≤ u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists
theorem exists_le_of_tendsto_atBot (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' ≤ b := exists_le_of_tendsto_atTop (β := βᵒᵈ) h
theorem exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a' ≥ a, b < u a' := by
  cases' exists_gt b with b' hb'
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩
theorem exists_lt_of_tendsto_atBot [NoMinOrder β] (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' < b := exists_lt_of_tendsto_atTop (β := βᵒᵈ) h
end IsDirected
section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {F : Filter β} {u : α → β}
theorem inf_map_atBot_neBot_iff : NeBot (F ⊓ map u atBot) ↔ ∀ U ∈ F, ∀ N, ∃ n ≤ N, u n ∈ U :=
  inf_map_atTop_neBot_iff (α := αᵒᵈ)
end IsCodirected
theorem high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β} (hu : Tendsto u atTop atTop) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n := by
  intro N
  obtain ⟨k : ℕ, - : k ≤ N, hku : ∀ l ≤ N, u l ≤ u k⟩ : ∃ k ≤ N, ∀ l ≤ N, u l ≤ u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : ∃ n ≥ N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : ℕ, hnN : n ≥ N, hnk : u k < u n, hn_min : ∀ m, m < n → N ≤ m → u m ≤ u k⟩ :
      ∃ n ≥ N, u k < u n ∧ ∀ m, m < n → N ≤ m → u m ≤ u k := by
    rcases Nat.findX ex with ⟨n, ⟨hnN, hnk⟩, hn_min⟩
    push_neg at hn_min
    exact ⟨n, hnN, hnk, hn_min⟩
  use n, hnN
  rintro (l : ℕ) (hl : l < n)
  have hlk : u l ≤ u k := by
    cases' (le_total l N : l ≤ N ∨ N ≤ l) with H H
    · exact hku l H
    · exact hn_min l hl H
  calc
    u l ≤ u k := hlk
    _ < u n := hnk
theorem low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β} (hu : Tendsto u atTop atBot) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u n < u k :=
  @high_scores βᵒᵈ _ _ _ hu
theorem frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ᶠ n in atTop, ∀ k < n, u k < u n := by
  simpa [frequently_atTop] using high_scores hu
theorem frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atBot) : ∃ᶠ n in atTop, ∀ k < n, u n < u k :=
  @frequently_high_scores βᵒᵈ _ _ _ hu
theorem strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩
theorem strictMono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)
theorem _root_.StrictMono.tendsto_atTop {φ : ℕ → ℕ} (h : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_mono h.id_le tendsto_id
theorem _root_.Monotone.upperBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    upperBounds (range (f ∘ g)) = upperBounds (range f) := by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, b ≤ g a := (hg.eventually_ge_atTop b).exists
  exact (hf ha).trans <| hc <| mem_range_self _
theorem _root_.Monotone.lowerBounds_range_comp_tendsto_atBot [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atBot) :
    lowerBounds (range (f ∘ g)) = lowerBounds (range f) :=
  hf.dual.upperBounds_range_comp_tendsto_atTop hg
theorem _root_.Antitone.lowerBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    lowerBounds (range (f ∘ g)) = lowerBounds (range f) :=
  hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg
theorem _root_.Antitone.upperBounds_range_comp_tendsto_atBot [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atBot) :
    upperBounds (range (f ∘ g)) = upperBounds (range f) :=
  hf.dual.lowerBounds_range_comp_tendsto_atTop hg
theorem _root_.Monotone.ciSup_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range, ← csInf_upperBounds_range,
    ← hf.upperBounds_range_comp_tendsto_atTop hg, Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]
theorem _root_.Monotone.ciInf_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop hb hg
theorem _root_.Antitone.ciSup_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop hb hg
theorem _root_.Antitone.ciInf_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atBot hb hg
theorem _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup, iSup, csSup_of_not_bddAbove, csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]
theorem _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg
theorem _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg
theorem _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg
theorem _root_.Monotone.iSup_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg
theorem _root_.Monotone.iInf_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg
theorem _root_.Antitone.iSup_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg
theorem _root_.Antitone.iInf_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg
theorem _root_.Monotone.iUnion_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atTop hf
theorem _root_.Monotone.iInter_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atBot hf
theorem _root_.Antitone.iInter_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atTop hf
theorem _root_.Antitone.iUnion_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atBot hf
theorem tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)
    (h : ∀ b, ∃ a, b ≤ f a) : Tendsto f atTop atTop :=
  tendsto_iInf.2 fun b =>
    tendsto_principal.2 <|
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')
theorem tendsto_atTop_atBot_of_antitone [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f)
    (h : ∀ b, ∃ a, f a ≤ b) : Tendsto f atTop atBot :=
  @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h
theorem tendsto_atBot_atBot_of_monotone [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)
    (h : ∀ b, ∃ a, f a ≤ b) : Tendsto f atBot atBot :=
  tendsto_iInf.2 fun b => tendsto_principal.2 <|
    let ⟨a, ha⟩ := h b; mem_of_superset (mem_atBot a) fun _a' ha' => le_trans (hf ha') ha
theorem tendsto_atBot_atTop_of_antitone [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f)
    (h : ∀ b, ∃ a, b ≤ f a) : Tendsto f atBot atTop :=
  @tendsto_atBot_atBot_of_monotone _ βᵒᵈ _ _ _ hf h
section IsDirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] {f : α → β} {l : Filter β}
theorem tendsto_atTop' : Tendsto f atTop l ↔ ∀ s ∈ l, ∃ a, ∀ b ≥ a, f b ∈ s := by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]
theorem tendsto_atTop_principal {s : Set β} : Tendsto f atTop (𝓟 s) ↔ ∃ N, ∀ n ≥ N, f n ∈ s := by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]
variable [Preorder β]
theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
  tendsto_iInf.trans <| forall_congr' fun _ => tendsto_atTop_principal
theorem tendsto_atTop_atBot : Tendsto f atTop atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → f a ≤ b :=
  tendsto_atTop_atTop (β := βᵒᵈ)
theorem tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) :
    Tendsto f atTop atTop ↔ ∀ b : β, ∃ a, b ≤ f a :=
  tendsto_atTop_atTop.trans <| forall_congr' fun _ => exists_congr fun a =>
    ⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h <| hf ha'⟩
theorem tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) :
    Tendsto f atTop atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf
end IsDirected
section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {f : α → β} {l : Filter β}
theorem tendsto_atBot' : Tendsto f atBot l ↔ ∀ s ∈ l, ∃ a, ∀ b ≤ a, f b ∈ s :=
  tendsto_atTop' (α := αᵒᵈ)
theorem tendsto_atBot_principal {s : Set β} : Tendsto f atBot (𝓟 s) ↔ ∃ N, ∀ n ≤ N, f n ∈ s :=
  tendsto_atTop_principal (α := αᵒᵈ) (β := βᵒᵈ)
variable [Preorder β]
theorem tendsto_atBot_atTop : Tendsto f atBot atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, a ≤ i → b ≤ f a :=
  tendsto_atTop_atTop (α := αᵒᵈ)
theorem tendsto_atBot_atBot : Tendsto f atBot atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, a ≤ i → f a ≤ b :=
  tendsto_atTop_atTop (α := αᵒᵈ) (β := βᵒᵈ)
theorem tendsto_atBot_atBot_iff_of_monotone (hf : Monotone f) :
    Tendsto f atBot atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atBot_atBot.trans <| forall_congr' fun _ => exists_congr fun a =>
    ⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans (hf ha') h⟩
theorem tendsto_atBot_atTop_iff_of_antitone (hf : Antitone f) :
    Tendsto f atBot atTop ↔ ∀ b : β, ∃ a, b ≤ f a :=
  tendsto_atBot_atBot_iff_of_monotone (β := βᵒᵈ) hf
end IsCodirected
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone
alias _root_.Monotone.tendsto_atBot_atBot := tendsto_atBot_atBot_of_monotone
alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone
alias _root_.Monotone.tendsto_atBot_atBot_iff := tendsto_atBot_atBot_iff_of_monotone
theorem comap_embedding_atTop [Preorder β] [Preorder γ] {e : β → γ}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) : comap e atTop = atTop :=
  le_antisymm
    (le_iInf fun b =>
      le_principal_iff.2 <| mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap
theorem comap_embedding_atBot [Preorder β] [Preorder γ] {e : β → γ}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, e b ≤ c) : comap e atBot = atBot :=
  @comap_embedding_atTop βᵒᵈ γᵒᵈ _ _ e (Function.swap hm) hu
theorem tendsto_atTop_embedding [Preorder β] [Preorder γ] {f : α → β} {e : β → γ} {l : Filter α}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) :
    Tendsto (e ∘ f) l atTop ↔ Tendsto f l atTop := by
  rw [← comap_embedding_atTop hm hu, tendsto_comap_iff]
theorem tendsto_atBot_embedding [Preorder β] [Preorder γ] {f : α → β} {e : β → γ} {l : Filter α}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, e b ≤ c) :
    Tendsto (e ∘ f) l atBot ↔ Tendsto f l atBot :=
  @tendsto_atTop_embedding α βᵒᵈ γᵒᵈ _ _ f e l (Function.swap hm) hu
theorem tendsto_finset_range : Tendsto Finset.range atTop atTop :=
  Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range
theorem atTop_finset_eq_iInf : (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x}) := by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
      le_principal_iff.2 <| mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici, Finset.le_iff_subset,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id
theorem tendsto_atTop_finset_of_monotone [Preorder β] {f : β → Finset α} (h : Monotone f)
    (h' : ∀ x : α, ∃ n, x ∈ f n) : Tendsto f atTop atTop := by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')
alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone
theorem tendsto_finset_image_atTop_atTop [DecidableEq β] {i : β → γ} {j : γ → β}
    (h : Function.LeftInverse j i) : Tendsto (Finset.image j) atTop atTop :=
  (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩
theorem tendsto_finset_preimage_atTop_atTop {f : α → β} (hf : Function.Injective f) :
    Tendsto (fun s : Finset β => s.preimage f (hf.injOn)) atTop atTop :=
  (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
    ⟨{f x}, Finset.mem_preimage.2 <| Finset.mem_singleton_self _⟩
theorem prod_atTop_atTop_eq [Preorder α] [Preorder β] :
    (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β)) := by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm
instance instIsCountablyGeneratedAtTopProd [Preorder α] [IsCountablyGenerated (atTop : Filter α)]
    [Preorder β] [IsCountablyGenerated (atTop : Filter β)] :
    IsCountablyGenerated (atTop : Filter (α × β)) := by
  rw [← prod_atTop_atTop_eq]
  infer_instance
lemma tendsto_finset_prod_atTop :
    Tendsto (fun (p : Finset ι × Finset ι') ↦ p.1 ×ˢ p.2) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product
theorem prod_atBot_atBot_eq [Preorder α] [Preorder β] :
    (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β)) :=
  @prod_atTop_atTop_eq αᵒᵈ βᵒᵈ _ _
instance instIsCountablyGeneratedAtBotProd [Preorder α] [IsCountablyGenerated (atBot : Filter α)]
    [Preorder β] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (atBot : Filter (α × β)) := by
  rw [← prod_atBot_atBot_eq]
  infer_instance
theorem prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) : map u₁ atTop ×ˢ map u₂ atTop = map (Prod.map u₁ u₂) atTop := by
  rw [prod_map_map_eq, prod_atTop_atTop_eq, Prod.map_def]
theorem prod_map_atBot_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) : map u₁ atBot ×ˢ map u₂ atBot = map (Prod.map u₁ u₂) atBot :=
  @prod_map_atTop_eq _ _ β₁ᵒᵈ β₂ᵒᵈ _ _ _ _
theorem Tendsto.subseq_mem {F : Filter α} {V : ℕ → Set α} (h : ∀ n, V n ∈ F) {u : ℕ → α}
    (hu : Tendsto u atTop F) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ V n :=
  extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : ∀ n, ∃ N, ∀ k ≥ N, u k ∈ V n)
theorem tendsto_atBot_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact tendsto_id.prod_mk tendsto_id
theorem tendsto_atTop_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prod_mk tendsto_id
theorem Tendsto.prod_map_prod_atBot [Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}
    {g : β → γ} (hf : Tendsto f F atBot) (hg : Tendsto g G atBot) :
    Tendsto (Prod.map f g) (F ×ˢ G) atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map hg
theorem Tendsto.prod_map_prod_atTop [Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}
    {g : β → γ} (hf : Tendsto f F atTop) (hg : Tendsto g G atTop) :
    Tendsto (Prod.map f g) (F ×ˢ G) atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map hg
theorem Tendsto.prod_atBot [Preorder α] [Preorder γ] {f g : α → γ}
    (hf : Tendsto f atBot atBot) (hg : Tendsto g atBot atBot) :
    Tendsto (Prod.map f g) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map_prod_atBot hg
theorem Tendsto.prod_atTop [Preorder α] [Preorder γ] {f g : α → γ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (Prod.map f g) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg
theorem eventually_atBot_prod_self [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k l, k ≤ a → l ≤ a → p (k, l) := by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]
theorem eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k l, a ≤ k → a ≤ l → p (k, l) :=
  eventually_atBot_prod_self (α := αᵒᵈ)
theorem eventually_atBot_prod_self'  [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k ≤ a, ∀ l ≤ a, p (k, l) := by
  simp only [eventually_atBot_prod_self, forall_cond_comm]
theorem eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k ≥ a, ∀ l ≥ a, p (k, l) := by
  simp only [eventually_atTop_prod_self, forall_cond_comm]
theorem eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atTop, p x) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, p (k, l) := by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry
theorem eventually_atBot_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atBot, p x) : ∀ᶠ k in atBot, ∀ᶠ l in atBot, p (k, l) :=
  @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp
theorem map_atTop_eq_of_gc_preorder
    [Preorder α] [IsDirected α (· ≤ ·)] [Preorder β] [IsDirected β (· ≤ ·)] {f : α → β}
    (hf : Monotone f) (b : β)
    (hgi : ∀ c ≥ b, ∃ x, f x = c ∧ ∀ a, f a ≤ c ↔ a ≤ x) : map f atTop = atTop := by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c ↦ ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
    intro a _
    filter_upwards [eventually_ge_atTop (f a), eventually_ge_atTop b] with c hac hbc
    exact ⟨g c, (hgle _ hbc _).1 hac, hfg _ hbc⟩
theorem map_atTop_eq_of_gc
    [Preorder α] [IsDirected α (· ≤ ·)] [PartialOrder β] [IsDirected β (· ≤ ·)]
    {f : α → β} (g : β → α) (b : β) (hf : Monotone f)
    (gc : ∀ a, ∀ c ≥ b, f a ≤ c ↔ a ≤ g c) (hgi : ∀ c ≥ b, c ≤ f (g c)) :
    map f atTop = atTop :=
  map_atTop_eq_of_gc_preorder hf b fun c hc ↦
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩
theorem map_atBot_eq_of_gc_preorder
    [Preorder α] [IsDirected α (· ≥ ·)] [Preorder β] [IsDirected β (· ≥ ·)] {f : α → β}
    (hf : Monotone f) (b : β)
    (hgi : ∀ c ≤ b, ∃ x, f x = c ∧ ∀ a, c ≤ f a ↔ x ≤ a) : map f atBot = atBot :=
  map_atTop_eq_of_gc_preorder (α := αᵒᵈ) (β := βᵒᵈ) hf.dual _ hgi
theorem map_atBot_eq_of_gc [Preorder α] [IsDirected α (· ≥ ·)]
    [PartialOrder β] [IsDirected β (· ≥ ·)] {f : α → β} (g : β → α) (b' : β)
    (hf : Monotone f) (gc : ∀ a, ∀ b ≤ b', b ≤ f a ↔ g b ≤ a) (hgi : ∀ b ≤ b', f (g b) ≤ b) :
    map f atBot = atBot :=
  map_atTop_eq_of_gc (α := αᵒᵈ) (β := βᵒᵈ) _ _ hf.dual gc hgi
theorem map_val_atTop_of_Ici_subset [Preorder α] [IsDirected α (· ≤ ·)] {a : α} {s : Set α}
    (h : Ici a ⊆ s) : map ((↑) : s → α) atTop = atTop := by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· ≤ ·) s := fun x _ y _ ↦
    ⟨f a (f x y), h <| hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirected s (· ≤ ·) := by
    rw [directedOn_iff_directed] at this
    rwa [← directed_id_iff]
  refine map_atTop_eq_of_gc_preorder (Subtype.mono_coe _) a fun c hc ↦ ?_
  exact ⟨⟨c, h hc⟩, rfl, fun _ ↦ .rfl⟩
@[simp]
theorem _root_.Nat.map_cast_int_atTop : map ((↑) : ℕ → ℤ) atTop = atTop := by
  refine map_atTop_eq_of_gc_preorder (fun _ _ ↦ Int.ofNat_le.2) 0 fun n hn ↦ ?_
  lift n to ℕ using hn
  exact ⟨n, rfl, fun _ ↦ Int.ofNat_le⟩
@[simp]
theorem map_val_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    map ((↑) : Ici a → α) atTop = atTop :=
  map_val_atTop_of_Ici_subset Subset.rfl
@[simp]
theorem map_val_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)] [NoMaxOrder α] (a : α) :
    map ((↑) : Ioi a → α) atTop = atTop :=
  let ⟨_b, hb⟩ := exists_gt a
  map_val_atTop_of_Ici_subset <| Ici_subset_Ioi.2 hb
theorem atTop_Ioi_eq [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    atTop = comap ((↑) : Ioi a → α) atTop := by
  rcases isEmpty_or_nonempty (Ioi a) with h|⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]
theorem atTop_Ici_eq [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    atTop = comap ((↑) : Ici a → α) atTop := by
  rw [← map_val_Ici_atTop a, comap_map Subtype.coe_injective]
@[simp]
theorem map_val_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)] [NoMinOrder α] (a : α) :
    map ((↑) : Iio a → α) atBot = atBot :=
  map_val_Ioi_atTop (OrderDual.toDual a)
theorem atBot_Iio_eq [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    atBot = comap ((↑) : Iio a → α) atBot :=
  atTop_Ioi_eq (OrderDual.toDual a)
@[simp]
theorem map_val_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    map ((↑) : Iic a → α) atBot = atBot :=
  map_val_Ici_atTop (OrderDual.toDual a)
theorem atBot_Iic_eq [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    atBot = comap ((↑) : Iic a → α) atBot :=
  atTop_Ici_eq (OrderDual.toDual a)
theorem tendsto_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : β → Ioi a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ioi_eq, tendsto_comap_iff, Function.comp_def]
theorem tendsto_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : β → Iio a} {l : Filter β} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l atBot :=
  tendsto_Ioi_atTop (α := αᵒᵈ)
theorem tendsto_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : β → Ici a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ici_eq, tendsto_comap_iff, Function.comp_def]
theorem tendsto_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : β → Iic a} {l : Filter β} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l atBot :=
  tendsto_Ici_atTop (α := αᵒᵈ)
@[simp]
theorem tendsto_comp_val_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)] [NoMaxOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ioi a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ioi_atTop a, tendsto_map'_iff, Function.comp_def]
@[simp]
theorem tendsto_comp_val_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ici a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ici_atTop a, tendsto_map'_iff, Function.comp_def]
@[simp]
theorem tendsto_comp_val_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)] [NoMinOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Iio a => f x) atBot l ↔ Tendsto f atBot l :=
  tendsto_comp_val_Ioi_atTop (α := αᵒᵈ)
@[simp]
theorem tendsto_comp_val_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Iic a => f x) atBot l ↔ Tendsto f atBot l :=
  tendsto_comp_val_Ici_atTop (α := αᵒᵈ)
theorem map_add_atTop_eq_nat (k : ℕ) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]
theorem map_sub_atTop_eq_nat (k : ℕ) : map (fun a => a - k) atTop = atTop :=
  map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]
theorem tendsto_add_atTop_nat (k : ℕ) : Tendsto (fun a => a + k) atTop atTop :=
  le_of_eq (map_add_atTop_eq_nat k)
theorem tendsto_sub_atTop_nat (k : ℕ) : Tendsto (fun a => a - k) atTop atTop :=
  le_of_eq (map_sub_atTop_eq_nat k)
theorem tendsto_add_atTop_iff_nat {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_add_atTop_eq_nat]
theorem map_div_atTop_eq_nat (k : ℕ) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, add_zero]; omega
theorem tendsto_atTop_atTop_of_monotone' [Preorder ι] [LinearOrder α] {u : ι → α} (h : Monotone u)
    (H : ¬BddAbove (range u)) : Tendsto u atTop atTop := by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩
theorem tendsto_atBot_atBot_of_monotone' [Preorder ι] [LinearOrder α] {u : ι → α} (h : Monotone u)
    (H : ¬BddBelow (range u)) : Tendsto u atBot atBot :=
  @tendsto_atTop_atTop_of_monotone' ιᵒᵈ αᵒᵈ _ _ _ h.dual H
section IsDirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] [Preorder β] {f : α → β}
theorem unbounded_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f atTop atTop) :
    ¬BddAbove (range f) := by
  rintro ⟨M, hM⟩
  cases' mem_atTop_sets.mp (h <| Ioi_mem_atTop M) with a ha
  apply lt_irrefl M
  calc
    M < f a := ha a le_rfl
    _ ≤ M := hM (Set.mem_range_self a)
theorem unbounded_of_tendsto_atBot [NoMinOrder β] (h : Tendsto f atTop atBot) :
    ¬BddBelow (range f) := unbounded_of_tendsto_atTop (β := βᵒᵈ) h
end IsDirected
section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] [Preorder β] {f : α → β}
theorem unbounded_of_tendsto_atTop' [NoMaxOrder β] (h : Tendsto f atBot atTop) :
    ¬BddAbove (range f) := unbounded_of_tendsto_atTop (α := αᵒᵈ) h
theorem unbounded_of_tendsto_atBot' [NoMinOrder β] (h : Tendsto f atBot atBot) :
    ¬BddBelow (range f) := unbounded_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) h
end IsCodirected
theorem tendsto_atTop_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι → α}
    (h : Monotone u) [NeBot l] (hu : Tendsto u l atTop) : Tendsto u atTop atTop :=
  h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists
theorem tendsto_atBot_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι → α}
    (h : Monotone u) [NeBot l] (hu : Tendsto u l atBot) : Tendsto u atBot atBot :=
  @tendsto_atTop_of_monotone_of_filter ιᵒᵈ αᵒᵈ _ _ _ _ h.dual _ hu
theorem tendsto_atTop_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι → α} {φ : ι' → ι}
    (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l atTop) :
    Tendsto u atTop atTop :=
  tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)
theorem tendsto_atBot_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι → α} {φ : ι' → ι}
    (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l atBot) :
    Tendsto u atBot atBot :=
  tendsto_atBot_of_monotone_of_filter h (tendsto_map' H)
theorem HasAntitoneBasis.eventually_subset [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {t : Set α} (ht : t ∈ l) : ∀ᶠ i in atTop, s i ⊆ t :=
  let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi
protected theorem HasAntitoneBasis.tendsto [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {φ : ι → α} (h : ∀ i : ι, φ i ∈ s i) : Tendsto φ atTop l :=
  fun _t ht => mem_map.2 <| (hl.eventually_subset ht).mono fun i hi => hi (h i)
theorem HasAntitoneBasis.comp_mono [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Preorder ι']
    {l : Filter α}
    {s : ι' → Set α} (hs : l.HasAntitoneBasis s) {φ : ι → ι'} (φ_mono : Monotone φ)
    (hφ : Tendsto φ atTop atTop) : l.HasAntitoneBasis (s ∘ φ) :=
  ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩
theorem HasAntitoneBasis.comp_strictMono {l : Filter α} {s : ℕ → Set α} (hs : l.HasAntitoneBasis s)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : l.HasAntitoneBasis (s ∘ φ) :=
  hs.comp_mono hφ.monotone hφ.tendsto_atTop
theorem HasAntitoneBasis.subbasis_with_rel {f : Filter α} {s : ℕ → Set α}
    (hs : f.HasAntitoneBasis s) {r : ℕ → ℕ → Prop} (hr : ∀ m, ∀ᶠ n in atTop, r m n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ ⦃m n⦄, m < n → r (φ m) (φ n)) ∧ f.HasAntitoneBasis (s ∘ φ) := by
  rsuffices ⟨φ, hφ, hrφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m n, m < n → r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : ∀ t : Set ℕ, t.Finite → ∀ᶠ n in atTop, ∀ m ∈ t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (eventually_gt_atTop m).and (hr _)
  rcases seq_of_forall_finite_exists fun t ht => (this t ht).exists with ⟨φ, hφ⟩
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_swap.2 hφ.1, forall_swap.2 hφ.2⟩
theorem exists_seq_tendsto (f : Filter α) [IsCountablyGenerated f] [NeBot f] :
    ∃ x : ℕ → α, Tendsto x atTop f := by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩
theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α]
    [IsDirected α (· ≤ ·)] [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧ Tendsto xs atTop atTop := by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : ℕ → α := fun n => (List.range n).foldl (fun x n ↦ c x (ys n)) (ys 0)
  have hsucc (n : ℕ) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hsucc]
    apply hleft
  · refine (tendsto_add_atTop_iff_nat 1).1 <| tendsto_atTop_mono (fun n ↦ ?_) h
    rw [hsucc]
    apply hright
theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type*) [Preorder α] [Nonempty α]
    [IsDirected α (· ≥ ·)] [(atBot : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Antitone xs ∧ Tendsto xs atTop atBot :=
  exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ
theorem tendsto_iff_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    Tendsto f k l ↔ ∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l := by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf, tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnmem, hmem⟩
  exact hnmem hmem
theorem tendsto_of_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    (∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l) → Tendsto f k l :=
  tendsto_iff_seq_tendsto.2
theorem eventually_iff_seq_eventually {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∀ᶠ n in l, p n) ↔ ∀ x : ℕ → ι, Tendsto x atTop l → ∀ᶠ n : ℕ in atTop, p (x n) := by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})
theorem frequently_iff_seq_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ x : ℕ → ι, Tendsto x atTop l ∧ ∃ᶠ n : ℕ in atTop, p (x n) := by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push_neg; rfl
theorem subseq_forall_of_frequently {ι : Type*} {x : ℕ → ι} {p : ι → Prop} {l : Filter ι}
    (h_tendsto : Tendsto x atTop l) (h : ∃ᶠ n in atTop, p (x n)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n => x (ns n)) atTop l ∧ ∀ n, p (x (ns n)) := by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩
theorem exists_seq_forall_of_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] (h : ∃ᶠ n in l, p n) :
    ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) := by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩
lemma frequently_iff_seq_forall {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) :=
  ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ ↦
    hnsl.frequently <| Frequently.of_forall hpns⟩
theorem tendsto_of_subseq_tendsto {ι : Type*} {x : ι → α} {f : Filter α} {l : Filter ι}
    [l.IsCountablyGenerated]
    (hxy : ∀ ns : ℕ → ι, Tendsto ns atTop l →
      ∃ ms : ℕ → ℕ, Tendsto (fun n => x (ns <| ms n)) atTop f) :
    Tendsto x l f := by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : ∃ s ∈ f, ∃ᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_nmem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto ↦ ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
  exact absurd hn <| hy_freq _
theorem subseq_tendsto_of_neBot {f : Filter α} [IsCountablyGenerated f] {u : ℕ → α}
    (hx : NeBot (f ⊓ map u atTop)) : ∃ θ : ℕ → ℕ, StrictMono θ ∧ Tendsto (u ∘ θ) atTop f := by
  rw [← Filter.push_pull', map_neBot_iff] at hx
  rcases exists_seq_tendsto (comap u f ⊓ atTop) with ⟨φ, hφ⟩
  rw [tendsto_inf, tendsto_comap_iff] at hφ
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.2
  exact ⟨φ ∘ ψ, hψφ, hφ.1.comp hψ.tendsto_atTop⟩
end Filter
open Filter Finset
theorem Monotone.piecewise_eventually_eq_iUnion {β : α → Type*} [Preorder ι] {s : ι → Set α}
    [∀ i, DecidablePred (· ∈ s i)] [DecidablePred (· ∈ ⋃ i, s i)]
    (hs : Monotone s) (f g : (a : α) → β a) (a : α) :
    ∀ᶠ i in atTop, (s i).piecewise f g a = (⋃ i, s i).piecewise f g a := by
  rcases em (∃ i, a ∈ s i) with ⟨i, hi⟩ | ha
  · refine (eventually_ge_atTop i).mono fun j hij ↦ ?_
    simp only [Set.piecewise_eq_of_mem, hs hij hi, subset_iUnion _ _ hi]
  · filter_upwards with i
    simp only [Set.piecewise_eq_of_not_mem, not_exists.1 ha i, mt mem_iUnion.1 ha,
      not_false_eq_true, exists_false]
theorem Antitone.piecewise_eventually_eq_iInter {β : α → Type*} [Preorder ι] {s : ι → Set α}
    [∀ i, DecidablePred (· ∈ s i)] [DecidablePred (· ∈ ⋂ i, s i)]
    (hs : Antitone s) (f g : (a : α) → β a) (a : α) :
    ∀ᶠ i in atTop, (s i).piecewise f g a = (⋂ i, s i).piecewise f g a := by
  classical
  convert ← (compl_anti.comp hs).piecewise_eventually_eq_iUnion g f a using 3
  · convert congr_fun (Set.piecewise_compl (s _) g f) a
  · simp only [(· ∘ ·), ← compl_iInter, Set.piecewise_compl]
namespace Nat
theorem eventually_pow_lt_factorial_sub (c d : ℕ) : ∀ᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · congr 1
    omega
  refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le <|
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : ℕ)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)
theorem eventually_mul_pow_lt_factorial_sub (a c d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn
@[deprecated eventually_pow_lt_factorial_sub (since := "2024-09-25")]
theorem exists_pow_lt_factorial (c : ℕ) : ∃ n0 > 1, ∀ n ≥ n0, c ^ n < (n - 1)! :=
  let ⟨n0, h⟩ := (eventually_pow_lt_factorial_sub c 1).exists_forall_of_atTop
  ⟨max n0 2, by omega, fun n hn ↦ h n (by omega)⟩
@[deprecated eventually_mul_pow_lt_factorial_sub (since := "2024-09-25")]
theorem exists_mul_pow_lt_factorial (a : ℕ) (c : ℕ) : ∃ n0, ∀ n ≥ n0, a * c ^ n < (n - 1)! :=
  (eventually_mul_pow_lt_factorial_sub a c 1).exists_forall_of_atTop
end Nat