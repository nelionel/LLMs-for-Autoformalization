import Mathlib.Algebra.Ring.Pointwise.Set
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Order.Basic
open Set Filter TopologicalSpace Topology Function
open OrderDual (toDual ofDual)
variable {α β γ : Type*}
section LinearOrder
variable [TopologicalSpace α] [LinearOrder α]
section OrderTopology
variable [OrderTopology α]
open List in
theorem TFAE_mem_nhdsWithin_Ioi {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[>] a,
      s ∈ 𝓝[Ioc a b] a,
      s ∈ 𝓝[Ioo a b] a,
      ∃ u ∈ Ioc a b, Ioo a u ⊆ s,
      ∃ u ∈ Ioi a, Ioo a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsWithin_Ioi hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsWithin_Ioi hab]
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsWithin_Ioi ⟨le_refl a, hau⟩) hu
  tfae_have 1 → 4
  | h => by
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h with ⟨v, va, hv⟩
    rcases exists_Ico_subset_of_mem_nhds' va hab with ⟨u, au, hu⟩
    exact ⟨u, au, fun x hx => hv ⟨hu ⟨le_of_lt hx.1, hx.2⟩, hx.1⟩⟩
  tfae_finish
theorem mem_nhdsWithin_Ioi_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioc a u', Ioo a u ⊆ s :=
  (TFAE_mem_nhdsWithin_Ioi hu' s).out 0 3
theorem mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  (TFAE_mem_nhdsWithin_Ioi hu' s).out 0 4
theorem nhdsWithin_Ioi_basis' {a : α} (h : ∃ b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' h⟩
lemma nhdsWithin_Ioi_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  nhdsWithin_Ioi_basis' <| exists_gt a
theorem nhdsWithin_Ioi_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ ∃ b, a ⋖ b := by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax, not_isMax_iff] at ha
    simp only [(nhdsWithin_Ioi_basis' ha).eq_bot_iff, covBy_iff_Ioo_eq]
theorem mem_nhdsWithin_Ioi_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' hu'
theorem countable_setOf_isolated_right [SecondCountableTopology α] :
    { x : α | 𝓝[>] x = ⊥ }.Countable := by
  simp only [nhdsWithin_Ioi_eq_bot_iff, setOf_or]
  exact (subsingleton_isTop α).countable.union countable_setOf_covBy_right
theorem countable_setOf_isolated_left [SecondCountableTopology α] :
    { x : α | 𝓝[<] x = ⊥ }.Countable :=
  countable_setOf_isolated_right (α := αᵒᵈ)
theorem mem_nhdsWithin_Ioi_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioc a u ⊆ s := by
  rw [mem_nhdsWithin_Ioi_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩
open List in
theorem TFAE_mem_nhdsWithin_Iio {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[<] b,
        s ∈ 𝓝[Ico a b] b,
        s ∈ 𝓝[Ioo a b] b,
        ∃ l ∈ Ico a b, Ioo l b ⊆ s,
        ∃ l ∈ Iio b, Ioo l b ⊆ s] := by
  simpa only [exists_prop, OrderDual.exists, dual_Ioi, dual_Ioc, dual_Ioo] using
    TFAE_mem_nhdsWithin_Ioi h.dual (ofDual ⁻¹' s)
theorem mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Ico l' a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsWithin_Iio hl' s).out 0 3
theorem mem_nhdsWithin_Iio_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsWithin_Iio hl' s).out 0 4
theorem mem_nhdsWithin_Iio_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  let ⟨_, h⟩ := exists_lt a
  mem_nhdsWithin_Iio_iff_exists_Ioo_subset' h
theorem mem_nhdsWithin_Iio_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ico l a ⊆ s := by
  have : ofDual ⁻¹' s ∈ 𝓝[>] toDual a ↔ _ := mem_nhdsWithin_Ioi_iff_exists_Ioc_subset
  simpa only [OrderDual.exists, exists_prop, dual_Ioc] using this
theorem nhdsWithin_Iio_basis' {a : α} (h : ∃ b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsWithin_Iio_iff_exists_Ioo_subset' h⟩
theorem nhdsWithin_Iio_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  nhdsWithin_Iio_basis' <| exists_lt a
theorem nhdsWithin_Iio_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ ∃ b, b ⋖ a := by
    convert (config := {preTransparency := .default})
      nhdsWithin_Ioi_eq_bot_iff (a := OrderDual.toDual a) using 4
    exact ofDual_covBy_ofDual_iff
open List in
theorem TFAE_mem_nhdsWithin_Ici {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≥] a,
      s ∈ 𝓝[Icc a b] a,
      s ∈ 𝓝[Ico a b] a,
      ∃ u ∈ Ioc a b, Ico a u ⊆ s,
      ∃ u ∈ Ioi a , Ico a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsWithin_Ici hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsWithin_Ici hab]
  tfae_have 1 ↔ 5 := (nhdsWithin_Ici_basis' ⟨b, hab⟩).mem_iff
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 4
  | ⟨u, hua, hus⟩ => ⟨min u b, ⟨lt_min hua hab, min_le_right _ _⟩,
      (Ico_subset_Ico_right <| min_le_left _ _).trans hus⟩
  tfae_finish
theorem mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioc a u', Ico a u ⊆ s :=
  (TFAE_mem_nhdsWithin_Ici hu' s).out 0 3 (by norm_num) (by norm_num)
theorem mem_nhdsWithin_Ici_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  (TFAE_mem_nhdsWithin_Ici hu' s).out 0 4 (by norm_num) (by norm_num)
theorem mem_nhdsWithin_Ici_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsWithin_Ici_iff_exists_Ico_subset' hu'
theorem nhdsWithin_Ici_basis_Ico [NoMaxOrder α] (a : α) :
    (𝓝[≥] a).HasBasis (fun u => a < u) (Ico a) :=
  ⟨fun _ => mem_nhdsWithin_Ici_iff_exists_Ico_subset⟩
theorem nhdsWithin_Ici_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≥] a).HasBasis (a < ·) (Icc a) :=
  (nhdsWithin_Ici_basis _).to_hasBasis
    (fun _u hu ↦ (exists_between hu).imp fun _v hv ↦ hv.imp_right Icc_subset_Ico_right)
    fun u hu ↦ ⟨u, hu, Ico_subset_Icc_self⟩
theorem mem_nhdsWithin_Ici_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[≥] a ↔ ∃ u, a < u ∧ Icc a u ⊆ s :=
  nhdsWithin_Ici_basis_Icc.mem_iff
open List in
theorem TFAE_mem_nhdsWithin_Iic {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≤] b,
      s ∈ 𝓝[Icc a b] b,
      s ∈ 𝓝[Ioc a b] b,
      ∃ l ∈ Ico a b, Ioc l b ⊆ s,
      ∃ l ∈ Iio b, Ioc l b ⊆ s] := by
  simpa only [exists_prop, OrderDual.exists, dual_Ici, dual_Ioc, dual_Icc, dual_Ico] using
    TFAE_mem_nhdsWithin_Ici h.dual (ofDual ⁻¹' s)
theorem mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Ico l' a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsWithin_Iic hl' s).out 0 3 (by norm_num) (by norm_num)
theorem mem_nhdsWithin_Iic_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsWithin_Iic hl' s).out 0 4 (by norm_num) (by norm_num)
theorem mem_nhdsWithin_Iic_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsWithin_Iic_iff_exists_Ioc_subset' hl'
theorem mem_nhdsWithin_Iic_iff_exists_Icc_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[≤] a ↔ ∃ l, l < a ∧ Icc l a ⊆ s :=
  calc s ∈ 𝓝[≤] a ↔ ofDual ⁻¹' s ∈ 𝓝[≥] (toDual a) := Iff.rfl
  _ ↔ ∃ u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) ⊆ ofDual ⁻¹' s :=
    mem_nhdsWithin_Ici_iff_exists_Icc_subset
  _ ↔ ∃ l, l < a ∧ Icc l a ⊆ s := by simp only [dual_Icc]; rfl
theorem nhdsWithin_Iic_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≤] a).HasBasis (· < a) (Icc · a) :=
  ⟨fun _ ↦ mem_nhdsWithin_Iic_iff_exists_Icc_subset⟩
end OrderTopology
end LinearOrder
section LinearOrderedAddCommGroup
variable [TopologicalSpace α] [LinearOrderedAddCommGroup α] [OrderTopology α]
variable {l : Filter β} {f g : β → α}
theorem nhds_eq_iInf_abs_sub (a : α) : 𝓝 a = ⨅ r > 0, 𝓟 { b | |a - b| < r } := by
  simp only [nhds_eq_order, abs_lt, setOf_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.subLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.subRight a).iInf_congr fun x => ?_; simp [Iio]
theorem orderTopology_of_nhds_abs {α : Type*} [TopologicalSpace α] [LinearOrderedAddCommGroup α]
    (h_nhds : ∀ a : α, 𝓝 a = ⨅ r > 0, 𝓟 { b | |a - b| < r }) : OrderTopology α := by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  letI := Preorder.topology α; letI : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_abs_sub a).symm
theorem LinearOrderedAddCommGroup.tendsto_nhds {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ ∀ ε > (0 : α), ∀ᶠ b in x, |f b - a| < ε := by
  simp [nhds_eq_iInf_abs_sub, abs_sub_comm a]
theorem eventually_abs_sub_lt (a : α) {ε : α} (hε : 0 < ε) : ∀ᶠ x in 𝓝 a, |x - a| < ε :=
  (nhds_eq_iInf_abs_sub a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [abs_sub_comm, mem_principal_self])
theorem Filter.Tendsto.add_atTop {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop := by
  nontriviality α
  obtain ⟨C', hC'⟩ : ∃ C', C' < C := exists_lt C
  refine tendsto_atTop_add_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt
theorem Filter.Tendsto.add_atBot {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  Filter.Tendsto.add_atTop (α := αᵒᵈ) hf hg
theorem Filter.Tendsto.atTop_add {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x + g x) l atTop := by
  conv in _ + _ => rw [add_comm]
  exact hg.add_atTop hf
theorem Filter.Tendsto.atBot_add {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x + g x) l atBot := by
  conv in _ + _ => rw [add_comm]
  exact hg.add_atBot hf
theorem nhds_basis_abs_sub_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (0 : α) < ε) fun ε => { b | |b - a| < ε } := by
  simp only [nhds_eq_iInf_abs_sub, abs_sub_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩
theorem nhds_basis_Ioo_pos [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (0 : α) < ε) fun ε => Ioo (a - ε) (a + ε) := by
  convert nhds_basis_abs_sub_lt a
  simp only [Ioo, abs_lt, ← sub_lt_iff_lt_add, neg_lt_sub_iff_lt_add, sub_lt_comm]
theorem nhds_basis_Icc_pos [NoMaxOrder α] [DenselyOrdered α] (a : α) :
    (𝓝 a).HasBasis ((0 : α) < ·) fun ε ↦ Icc (a - ε) (a + ε) :=
  (nhds_basis_Ioo_pos a).to_hasBasis
    (fun _ε ε₀ ↦ let ⟨δ, δ₀, δε⟩ := exists_between ε₀
      ⟨δ, δ₀, Icc_subset_Ioo (sub_lt_sub_left δε _) (add_lt_add_left δε _)⟩)
    (fun ε ε₀ ↦ ⟨ε, ε₀, Ioo_subset_Icc_self⟩)
variable (α)
theorem nhds_basis_zero_abs_sub_lt [NoMaxOrder α] :
    (𝓝 (0 : α)).HasBasis (fun ε : α => (0 : α) < ε) fun ε => { b | |b| < ε } := by
  simpa using nhds_basis_abs_sub_lt (0 : α)
variable {α}
theorem nhds_basis_Ioo_pos_of_pos [NoMaxOrder α] {a : α} (ha : 0 < a) :
    (𝓝 a).HasBasis (fun ε : α => (0 : α) < ε ∧ ε ≤ a) fun ε => Ioo (a - ε) (a + ε) :=
  (nhds_basis_Ioo_pos a).restrict fun ε hε => ⟨min a ε, lt_min ha hε, min_le_left _ _,
    Ioo_subset_Ioo (sub_le_sub_left (min_le_right _ _) _) (add_le_add_left (min_le_right _ _) _)⟩
end LinearOrderedAddCommGroup
namespace Set.OrdConnected
variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
lemma mem_nhdsWithin_Ici [NoMaxOrder α] {S : Set α} (hS : OrdConnected S)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    S ∈ 𝓝[≥] x :=
  mem_nhdsWithin_Ici_iff_exists_Icc_subset.2 ⟨y, hxy, hS.out hx hy⟩
lemma mem_nhdsWithin_Ioi [NoMaxOrder α] {S : Set α} (hS : OrdConnected S)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    S ∈ 𝓝[>] x :=
  nhdsWithin_mono _ Ioi_subset_Ici_self <| hS.mem_nhdsWithin_Ici hx hy hxy
lemma mem_nhdsWithin_Iic [NoMinOrder α] {S : Set α} (hS : OrdConnected S)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    S ∈ 𝓝[≤] y :=
  mem_nhdsWithin_Iic_iff_exists_Icc_subset.2 ⟨x, hxy, hS.out hx hy⟩
lemma mem_nhdsWithin_Iio [NoMinOrder α] {S : Set α} (hS : OrdConnected S)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    S ∈ 𝓝[<] y :=
  nhdsWithin_mono _ Iio_subset_Iic_self <| hS.mem_nhdsWithin_Iic hx hy hxy
end OrdConnected
end Set