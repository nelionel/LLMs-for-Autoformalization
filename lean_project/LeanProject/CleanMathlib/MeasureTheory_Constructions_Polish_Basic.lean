import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.CountableSeparatingOn
import Mathlib.Topology.MetricSpace.Perfect
open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory
variable (α : Type*)
class StandardBorelSpace [MeasurableSpace α] : Prop where
  polish : ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α
class UpgradedStandardBorel extends MeasurableSpace α, TopologicalSpace α,
  BorelSpace α, PolishSpace α
noncomputable
def upgradeStandardBorel [MeasurableSpace α] [h : StandardBorelSpace α] :
    UpgradedStandardBorel α := by
  choose τ hb hp using h.polish
  constructor
theorem eq_borel_upgradeStandardBorel [MeasurableSpace α] [StandardBorelSpace α] :
    ‹MeasurableSpace α› = @borel _ (upgradeStandardBorel α).toTopologicalSpace :=
  @BorelSpace.measurable_eq _ (upgradeStandardBorel α).toTopologicalSpace _
    (upgradeStandardBorel α).toBorelSpace
variable {α}
section
variable [MeasurableSpace α]
instance (priority := 100) standardBorel_of_polish [τ : TopologicalSpace α]
    [BorelSpace α] [PolishSpace α] : StandardBorelSpace α := by exists τ
instance (priority := 100) standardBorelSpace_of_discreteMeasurableSpace [DiscreteMeasurableSpace α]
    [Countable α] : StandardBorelSpace α :=
  let _ : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  inferInstance
instance (priority := 100) countablyGenerated_of_standardBorel [StandardBorelSpace α] :
    MeasurableSpace.CountablyGenerated α :=
  letI := upgradeStandardBorel α
  inferInstance
instance (priority := 100) measurableSingleton_of_standardBorel [StandardBorelSpace α] :
    MeasurableSingletonClass α :=
  letI := upgradeStandardBorel α
  inferInstance
namespace StandardBorelSpace
variable {β : Type*} [MeasurableSpace β]
section instances
instance prod [StandardBorelSpace α] [StandardBorelSpace β] : StandardBorelSpace (α × β) :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance
instance pi_countable {ι : Type*} [Countable ι] {α : ι → Type*} [∀ n, MeasurableSpace (α n)]
    [∀ n, StandardBorelSpace (α n)] : StandardBorelSpace (∀ n, α n) :=
  letI := fun n => upgradeStandardBorel (α n)
  inferInstance
end instances
end StandardBorelSpace
end
variable {ι : Type*}
namespace MeasureTheory
variable [TopologicalSpace α]
irreducible_def AnalyticSet (s : Set α) : Prop :=
  s = ∅ ∨ ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = s
theorem analyticSet_empty : AnalyticSet (∅ : Set α) := by
  rw [AnalyticSet]
  exact Or.inl rfl
theorem analyticSet_range_of_polishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {f : β → α} (f_cont : Continuous f) : AnalyticSet (range f) := by
  cases isEmpty_or_nonempty β
  · rw [range_eq_empty]
    exact analyticSet_empty
  · rw [AnalyticSet]
    obtain ⟨g, g_cont, hg⟩ : ∃ g : (ℕ → ℕ) → β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine Or.inr ⟨f ∘ g, f_cont.comp g_cont, ?_⟩
    rw [hg.range_comp]
theorem _root_.IsOpen.analyticSet_image {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {s : Set β} (hs : IsOpen s) {f : β → α} (f_cont : Continuous f) : AnalyticSet (f '' s) := by
  rw [image_eq_range]
  haveI : PolishSpace s := hs.polishSpace
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)
theorem analyticSet_iff_exists_polishSpace_range {s : Set α} :
    AnalyticSet s ↔
      ∃ (β : Type) (h : TopologicalSpace β) (_ : @PolishSpace β h) (f : β → α),
        @Continuous _ _ h _ f ∧ range f = s := by
  constructor
  · intro h
    rw [AnalyticSet] at h
    cases' h with h h
    · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, ?_⟩
      rw [h]
      exact range_eq_empty _
    · exact ⟨ℕ → ℕ, inferInstance, inferInstance, h⟩
  · rintro ⟨β, h, h', f, f_cont, f_range⟩
    rw [← f_range]
    exact analyticSet_range_of_polishSpace f_cont
theorem AnalyticSet.image_of_continuousOn {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : ContinuousOn f s) : AnalyticSet (f '' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  rw [this]
  apply analyticSet_range_of_polishSpace
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self
theorem AnalyticSet.image_of_continuous {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
theorem AnalyticSet.iInter [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι → Set α}
    (hs : ∀ n, AnalyticSet (s n)) : AnalyticSet (⋂ n, s n) := by
  rcases hι with ⟨i₀⟩
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := ∀ n, β n
  let t : Set γ := ⋂ n, { x | f n (x n) = f i₀ (x i₀) }
  have t_closed : IsClosed t := by
    apply isClosed_iInter
    intro n
    exact
      isClosed_eq ((f_cont n).comp (continuous_apply n)) ((f_cont i₀).comp (continuous_apply i₀))
  haveI : PolishSpace t := t_closed.polishSpace
  let F : t → α := fun x => f i₀ ((x : γ) i₀)
  have F_cont : Continuous F := (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_val)
  have F_range : range F = ⋂ n : ι, s n := by
    apply Subset.antisymm
    · rintro y ⟨x, rfl⟩
      refine mem_iInter.2 fun n => ?_
      have : f n ((x : γ) n) = F x := (mem_iInter.1 x.2 n : _)
      rw [← this, ← f_range n]
      exact mem_range_self _
    · intro y hy
      have A : ∀ n, ∃ x : β n, f n x = y := by
        intro n
        rw [← mem_range, f_range n]
        exact mem_iInter.1 hy n
      choose x hx using A
      have xt : x ∈ t := by
        refine mem_iInter.2 fun n => ?_
        simp [hx]
      refine ⟨⟨x, xt⟩, ?_⟩
      exact hx i₀
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont
theorem AnalyticSet.iUnion [Countable ι] {s : ι → Set α} (hs : ∀ n, AnalyticSet (s n)) :
    AnalyticSet (⋃ n, s n) := by
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := Σn, β n
  let F : γ → α := fun ⟨n, x⟩ ↦ f n x
  have F_cont : Continuous F := continuous_sigma f_cont
  have F_range : range F = ⋃ n, s n := by
    simp only [γ, range_sigma_eq_iUnion_range, f_range]
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont
theorem _root_.IsClosed.analyticSet [PolishSpace α] {s : Set α} (hs : IsClosed s) :
    AnalyticSet s := by
  haveI : PolishSpace s := hs.polishSpace
  rw [← @Subtype.range_val α s]
  exact analyticSet_range_of_polishSpace continuous_subtype_val
theorem _root_.MeasurableSet.isClopenable [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) : IsClopenable s := by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
  · exact fun u _ h'u => h'u.compl
  · exact fun f _ _ hf => IsClopenable.iUnion hf
theorem _root_.MeasurableSet.analyticSet {α : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : MeasurableSet s) : AnalyticSet s := by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  have A := @IsClosed.analyticSet α t' t'_polish s s_closed
  convert @AnalyticSet.image_of_continuous α t' α t s A id (continuous_id_of_le t't)
  simp only [id, image_id']
theorem _root_.Measurable.exists_continuous {α β : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [tβ : TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : α → β} [SecondCountableTopology (range f)] (hf : Measurable f) :
    ∃ t' : TopologicalSpace α, t' ≤ t ∧ @Continuous α β t' tβ f ∧ @PolishSpace α t' := by
  obtain ⟨b, b_count, -, hb⟩ :
      ∃ b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  haveI : Countable b := b_count.to_subtype
  have : ∀ s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s ↦ by
    apply MeasurableSet.isClopenable
    exact hf.subtype_mk (hb.isOpen s.2).measurableSet
  choose T Tt Tpolish _ Topen using this
  obtain ⟨t', t'T, t't, t'_polish⟩ :
      ∃ t' : TopologicalSpace α, (∀ i, t' ≤ T i) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le (t := t) T Tt Tpolish
  refine ⟨t', t't, ?_, t'_polish⟩
  have : Continuous[t', _] (rangeFactorization f) :=
    hb.continuous_iff.2 fun s hs => t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩)
  exact continuous_subtype_val.comp this
theorem _root_.MeasurableSet.analyticSet_image {X Y : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {f : X → Y} [SecondCountableTopology (range f)] {s : Set X}
    (hs : MeasurableSet s) (hf : Measurable f) : AnalyticSet (f '' s) := by
  letI := upgradeStandardBorel X
  rw [eq_borel_upgradeStandardBorel X] at hs
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  letI m' : MeasurableSpace X := @borel _ τ'
  haveI b' : BorelSpace X := ⟨rfl⟩
  have hle := borel_anti hle
  exact (hle _ hs).analyticSet.image_of_continuous hfc
protected lemma AnalyticSet.preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [T2Space Y] {s : Set Y} (hs : AnalyticSet s) {f : X → Y} (hf : Continuous f) :
    AnalyticSet (f ⁻¹' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨Z, _, _, g, hg, rfl⟩
  have : IsClosed {x : X × Z | f x.1 = g x.2} := isClosed_eq hf.fst' hg.snd'
  convert this.analyticSet.image_of_continuous continuous_fst
  ext x
  simp [eq_comm]
def MeasurablySeparable {α : Type*} [MeasurableSpace α] (s t : Set α) : Prop :=
  ∃ u, s ⊆ u ∧ Disjoint t u ∧ MeasurableSet u
theorem MeasurablySeparable.iUnion [Countable ι] {α : Type*} [MeasurableSpace α] {s t : ι → Set α}
    (h : ∀ m n, MeasurablySeparable (s m) (t n)) : MeasurablySeparable (⋃ n, s n) (⋃ m, t m) := by
  choose u hsu htu hu using h
  refine ⟨⋃ m, ⋂ n, u m n, ?_, ?_, ?_⟩
  · refine iUnion_subset fun m => subset_iUnion_of_subset m ?_
    exact subset_iInter fun n => hsu m n
  · simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro n m
    apply Disjoint.mono_right _ (htu m n)
    apply iInter_subset
  · refine MeasurableSet.iUnion fun m => ?_
    exact MeasurableSet.iInter fun n => hu m n
theorem measurablySeparable_range_of_disjoint [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f g : (ℕ → ℕ) → α} (hf : Continuous f) (hg : Continuous g)
    (h : Disjoint (range f) (range g)) : MeasurablySeparable (range f) (range g) := by
  by_contra hfg
  have I : ∀ n x y, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) →
      ∃ x' y', x' ∈ cylinder x n ∧ y' ∈ cylinder y n ∧
      ¬MeasurablySeparable (f '' cylinder x' (n + 1)) (g '' cylinder y' (n + 1)) := by
    intro n x y
    contrapose!
    intro H
    rw [← iUnion_cylinder_update x n, ← iUnion_cylinder_update y n, image_iUnion, image_iUnion]
    refine MeasurablySeparable.iUnion fun i j => ?_
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _)
  let A :=
    { p : ℕ × (ℕ → ℕ) × (ℕ → ℕ) //
      ¬MeasurablySeparable (f '' cylinder p.2.1 p.1) (g '' cylinder p.2.2 p.1) }
  have : ∀ p : A, ∃ q : A,
      q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1 ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1 := by
    rintro ⟨⟨n, x, y⟩, hp⟩
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩
    exact ⟨⟨⟨n + 1, x', y'⟩, h'⟩, rfl, hx', hy'⟩
  choose F hFn hFx hFy using this
  let p0 : A := ⟨⟨0, fun _ => 0, fun _ => 0⟩, by simp [hfg]⟩
  let p : ℕ → A := fun n => F^[n] p0
  have prec : ∀ n, p (n + 1) = F (p n) := fun n => by simp only [p, iterate_succ', Function.comp]
  have pn_fst : ∀ n, (p n).1.1 = n := by
    intro n
    induction' n with n IH
    · rfl
    · simp only [prec, hFn, IH]
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m + 1)).1.2.1 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m := by
      apply hFx (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m + 1)).1.2.2 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m := by
      apply hFy (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  set x : ℕ → ℕ := fun n => (p (n + 1)).1.2.1 n with hx
  set y : ℕ → ℕ := fun n => (p (n + 1)).1.2.2 n with hy
  have M : ∀ n, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    intro n
    convert (p n).2 using 3
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hx]
      exact (Ix i n hi).symm
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hy]
      exact (Iy i n hi).symm
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ :
      ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ g y ∈ v ∧ Disjoint u v := by
    apply t2_separation
    exact disjoint_iff_forall_ne.1 h (mem_range_self _) (mem_range_self _)
  letI : MetricSpace (ℕ → ℕ) := metricSpaceNatNat
  obtain ⟨εx, εxpos, hεx⟩ : ∃ (εx : ℝ), εx > 0 ∧ Metric.ball x εx ⊆ f ⁻¹' u := by
    apply Metric.mem_nhds_iff.1
    exact hf.continuousAt.preimage_mem_nhds (u_open.mem_nhds xu)
  obtain ⟨εy, εypos, hεy⟩ : ∃ (εy : ℝ), εy > 0 ∧ Metric.ball y εy ⊆ g ⁻¹' v := by
    apply Metric.mem_nhds_iff.1
    exact hg.continuousAt.preimage_mem_nhds (v_open.mem_nhds yv)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_min εxpos εypos) (by norm_num)
  have B : MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    refine ⟨u, ?_, ?_, u_open.measurableSet⟩
    · rw [image_subset_iff]
      apply Subset.trans _ hεx
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_left _ _))
    · refine Disjoint.mono_left ?_ huv.symm
      change g '' cylinder y n ⊆ v
      rw [image_subset_iff]
      apply Subset.trans _ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_right _ _))
  exact M n B
theorem AnalyticSet.measurablySeparable [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s t : Set α} (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) :
    MeasurablySeparable s t := by
  rw [AnalyticSet] at hs ht
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  · refine ⟨∅, Subset.refl _, by simp, MeasurableSet.empty⟩
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  · exact ⟨univ, subset_univ _, by simp, MeasurableSet.univ⟩
  exact measurablySeparable_range_of_disjoint f_cont g_cont h
theorem AnalyticSet.measurableSet_of_compl [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) : MeasurableSet s := by
  rcases hs.measurablySeparable hsc disjoint_compl_right with ⟨u, hsu, hdu, hmu⟩
  obtain rfl : s = u := hsu.antisymm (disjoint_compl_left_iff_subset.1 hdu)
  exact hmu
end MeasureTheory
namespace Measurable
open MeasurableSpace
variable {X Y Z β : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace Y] [T0Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace β]
  [MeasurableSpace Z]
theorem measurableSet_preimage_iff_of_surjective [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f) (hsurj : Surjective f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet s := by
  refine ⟨fun h => ?_, fun h => hf h⟩
  rcases exists_opensMeasurableSpace_of_countablySeparated Z with ⟨τ, _, _, _⟩
  apply AnalyticSet.measurableSet_of_compl
  · rw [← image_preimage_eq s hsurj]
    exact h.analyticSet_image hf
  · rw [← image_preimage_eq sᶜ hsurj]
    exact h.compl.analyticSet_image hf
theorem map_measurableSpace_eq [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = ‹MeasurableSpace Z› :=
  MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj
theorem map_measurableSpace_eq_borel [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  letI := borel Y; haveI : BorelSpace Y := ⟨rfl⟩
  exact d.map_measurableSpace_eq hsurj
theorem borelSpace_codomain [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : BorelSpace Y :=
  ⟨(hf.map_measurableSpace_eq hsurj).symm.trans <| hf.map_measurableSpace_eq_borel hsurj⟩
theorem measurableSet_preimage_iff_preimage_val {f : X → Z} [CountablySeparated (range f)]
    (hf : Measurable f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet ((↑) ⁻¹' s : Set (range f)) :=
  have hf' : Measurable (rangeFactorization f) := hf.subtype_mk
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s) surjective_onto_range
theorem measurableSet_preimage_iff_inter_range {f : X → Z} [CountablySeparated (range f)]
    (hf : Measurable f) (hr : MeasurableSet (range f)) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [hf.measurableSet_preimage_iff_preimage_val, inter_comm,
    ← (MeasurableEmbedding.subtype_coe hr).measurableSet_image, Subtype.image_preimage_coe]
theorem measurable_comp_iff_restrict {f : X → Z}
    [CountablySeparated (range f)]
    (hf : Measurable f) {g : Z → β} : Measurable (g ∘ f) ↔ Measurable (restrict (range f) g) :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)
theorem measurable_comp_iff_of_surjective [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f) (hsurj : Surjective f)
    {g : Z → β} : Measurable (g ∘ f) ↔ Measurable g :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)
end Measurable
theorem Continuous.map_eq_borel {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Surjective f) :
    MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  borelize Y
  exact hf.measurable.map_measurableSpace_eq hsurj
theorem Continuous.map_borel_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y] {f : X → Y} (hf : Continuous f)
    (hsurj : Surjective f) : MeasurableSpace.map f (borel X) = borel Y := by
  borelize X
  exact hf.map_eq_borel hsurj
instance Quotient.borelSpace {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Setoid X} [T0Space (Quotient s)] [SecondCountableTopology (Quotient s)] :
    BorelSpace (Quotient s) :=
  ⟨continuous_quotient_mk'.map_eq_borel Quotient.mk'_surjective⟩
@[to_additive AddCosetSpace.borelSpace]
instance CosetSpace.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)]
    [SecondCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N) := Quotient.borelSpace
@[to_additive]
instance QuotientGroup.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [TopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [N.Normal]
    [IsClosed (N : Set G)] : BorelSpace (G ⧸ N) :=
  ⟨continuous_mk.map_eq_borel mk_surjective⟩
namespace MeasureTheory
variable {γ : Type*}
theorem measurableSet_range_of_continuous_injective {β : Type*} [TopologicalSpace γ]
    [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {f : γ → β} (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableSet (range f) := by
  letI := upgradePolishSpace γ
  obtain ⟨b, b_count, b_nonempty, hb⟩ :
    ∃ b : Set (Set γ), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := exists_countable_basis γ
  haveI : Encodable b := b_count.toEncodable
  let A := { p : b × b // Disjoint (p.1 : Set γ) p.2 }
  have : ∀ p : A, ∃ q : Set β,
      f '' (p.1.1 : Set γ) ⊆ q ∧ Disjoint (f '' (p.1.2 : Set γ)) q ∧ MeasurableSet q := by
    intro p
    apply
      AnalyticSet.measurablySeparable ((hb.isOpen p.1.1.2).analyticSet_image f_cont)
        ((hb.isOpen p.1.2.2).analyticSet_image f_cont)
    exact Disjoint.image p.2 f_inj.injOn (subset_univ _) (subset_univ _)
  choose q hq1 hq2 q_meas using this
  let E : b → Set β := fun s =>
    closure (f '' s) ∩ ⋂ (t : b) (ht : Disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  let F : ℕ → Set β := fun n => ⋃ (s : b) (_ : IsBounded s.1 ∧ diam s.1 ≤ u n), E s
  suffices range f = ⋂ n, F n by
    have E_meas : ∀ s : b, MeasurableSet (E s) := by
      intro b
      refine isClosed_closure.measurableSet.inter ?_
      refine MeasurableSet.iInter fun s => ?_
      exact MeasurableSet.iInter fun hs => (q_meas _).diff (q_meas _)
    have F_meas : ∀ n, MeasurableSet (F n) := by
      intro n
      refine MeasurableSet.iUnion fun s => ?_
      exact MeasurableSet.iUnion fun _ => E_meas _
    rw [this]
    exact MeasurableSet.iInter fun n => F_meas n
  apply Subset.antisymm
  · rintro x ⟨y, rfl⟩
    refine mem_iInter.2 fun n => ?_
    obtain ⟨s, sb, ys, hs⟩ : ∃ (s : Set γ), s ∈ b ∧ y ∈ s ∧ s ⊆ ball y (u n / 2) := by
      apply hb.mem_nhds_iff.1
      exact ball_mem_nhds _ (half_pos (u_pos n))
    have diam_s : diam s ≤ u n := by
      apply (diam_mono hs isBounded_ball).trans
      convert diam_ball (x := y) (half_pos (u_pos n)).le
      ring
    refine mem_iUnion.2 ⟨⟨s, sb⟩, ?_⟩
    refine mem_iUnion.2 ⟨⟨isBounded_ball.subset hs, diam_s⟩, ?_⟩
    apply mem_inter (subset_closure (mem_image_of_mem _ ys))
    refine mem_iInter.2 fun t => mem_iInter.2 fun ht => ⟨?_, ?_⟩
    · apply hq1
      exact mem_image_of_mem _ ys
    · apply disjoint_left.1 (hq2 ⟨(t, ⟨s, sb⟩), ht.symm⟩)
      exact mem_image_of_mem _ ys
  · intro x hx
    have C1 : ∀ n, ∃ (s : b) (_ : IsBounded s.1 ∧ diam s.1 ≤ u n), x ∈ E s := fun n => by
      simpa only [F, mem_iUnion] using mem_iInter.1 hx n
    choose s hs hxs using C1
    have C2 : ∀ n, (s n).1.Nonempty := by
      intro n
      rw [nonempty_iff_ne_empty]
      intro hn
      have := (s n).2
      rw [hn] at this
      exact b_nonempty this
    choose y hy using C2
    have I : ∀ m n, ((s m).1 ∩ (s n).1).Nonempty := by
      intro m n
      rw [← not_disjoint_iff_nonempty_inter]
      by_contra! h
      have A : x ∈ q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩ :=
        haveI := mem_iInter.1 (hxs m).2 (s n)
        (mem_iInter.1 this h : _)
      have B : x ∈ q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩ :=
        haveI := mem_iInter.1 (hxs n).2 (s m)
        (mem_iInter.1 this h.symm : _)
      exact A.2 B.1
    have cauchy_y : CauchySeq y := by
      have : Tendsto (fun n => 2 * u n) atTop (𝓝 0) := by
        simpa only [mul_zero] using u_lim.const_mul 2
      refine cauchySeq_of_le_tendsto_0' (fun n => 2 * u n) (fun m n hmn => ?_) this
      rcases I m n with ⟨z, zsm, zsn⟩
      calc
        dist (y m) (y n) ≤ dist (y m) z + dist z (y n) := dist_triangle _ _ _
        _ ≤ u m + u n :=
          (add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
            ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2))
        _ ≤ 2 * u m := by linarith [u_anti.antitone hmn]
    haveI : Nonempty γ := ⟨y 0⟩
    let z := limUnder atTop y
    have y_lim : Tendsto y atTop (𝓝 z) := cauchy_y.tendsto_limUnder
    suffices f z = x by
      rw [← this]
      exact mem_range_self _
    by_contra! hne
    obtain ⟨v, w, v_open, w_open, fzv, xw, hvw⟩ := t2_separation hne
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > (0 : ℝ), ball z δ ⊆ f ⁻¹' v := by
      apply Metric.mem_nhds_iff.1
      exact f_cont.continuousAt.preimage_mem_nhds (v_open.mem_nhds fzv)
    obtain ⟨n, hn⟩ : ∃ n, u n + dist (y n) z < δ :=
      haveI : Tendsto (fun n => u n + dist (y n) z) atTop (𝓝 0) := by
        simpa only [add_zero] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim)
      ((tendsto_order.1 this).2 _ δpos).exists
    have fsnv : f '' s n ⊆ v := by
      rw [image_subset_iff]
      apply Subset.trans _ hδ
      intro a ha
      calc
        dist a z ≤ dist a (y n) + dist (y n) z := dist_triangle _ _ _
        _ ≤ u n + dist (y n) z :=
          (add_le_add_right ((dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2) _)
        _ < δ := hn
    have : x ∈ closure v := closure_mono fsnv (hxs n).1
    exact disjoint_left.1 (hvw.closure_left w_open) this xw
theorem _root_.IsClosed.measurableSet_image_of_continuousOn_injOn
    [TopologicalSpace γ] [PolishSpace γ] {β : Type*} [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {s : Set γ} (hs : IsClosed s) {f : γ → β}
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  rw [image_eq_range]
  haveI : PolishSpace s := IsClosed.polishSpace hs
  apply measurableSet_range_of_continuous_injective
  · rwa [continuousOn_iff_continuous_restrict] at f_cont
  · rwa [injOn_iff_injective] at f_inj
variable {α β : Type*} [MeasurableSpace β]
section
variable [tβ : TopologicalSpace β] [T2Space β] [MeasurableSpace α] {s : Set γ} {f : γ → β}
theorem _root_.MeasurableSet.image_of_continuousOn_injOn [OpensMeasurableSpace β]
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s)
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) f_inj
theorem _root_.MeasurableSet.image_of_measurable_injOn {f : γ → α}
    [MeasurableSpace.CountablySeparated α]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    (hs : MeasurableSet s) (f_meas : Measurable f) (f_inj : InjOn f s) :
    MeasurableSet (f '' s) := by
  letI := upgradeStandardBorel γ
  let tγ : TopologicalSpace γ := inferInstance
  rcases exists_opensMeasurableSpace_of_countablySeparated α with ⟨τ, _, _, _⟩
  obtain ⟨t', t't, f_cont, t'_polish⟩ :
      ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @Continuous γ _ t' _ f ∧ @PolishSpace γ t' :=
    f_meas.exists_continuous
  have M : MeasurableSet[@borel γ t'] s :=
    @Continuous.measurable γ γ t' (@borel γ t')
      (@BorelSpace.opensMeasurable γ t' (@borel γ t') (@BorelSpace.mk _ _ (borel γ) rfl))
      tγ _ _ _ (continuous_id_of_le t't) s hs
  exact
    @MeasurableSet.image_of_continuousOn_injOn γ
      _ _ _ _  s f _ t' t'_polish (@borel γ t') (@BorelSpace.mk _ _ (borel γ) rfl)
      M (@Continuous.continuousOn γ _ t' _ f s f_cont) f_inj
theorem _root_.Continuous.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn f_inj.injOn }
theorem _root_.ContinuousOn.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableEmbedding (s.restrict f) :=
  { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_restrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      have A : MeasurableSet (((↑) : s → γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
      have B : MeasurableSet (f '' (((↑) : s → γ) '' u)) :=
        A.image_of_continuousOn_injOn (f_cont.mono (Subtype.coe_image_subset s u))
          (f_inj.mono (Subtype.coe_image_subset s u))
      rwa [← image_comp] at B }
theorem _root_.Measurable.measurableEmbedding {f : γ → α}
    [MeasurableSpace.CountablySeparated α]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    (f_meas : Measurable f) (f_inj : Injective f) : MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas f_inj.injOn }
theorem borel_eq_borel_of_le {t t' : TopologicalSpace γ}
    (ht : PolishSpace (h := t)) (ht' : PolishSpace (h := t')) (hle : t ≤ t') :
    @borel _ t = @borel _ t' := by
  refine le_antisymm ?_ (borel_anti hle)
  intro s hs
  have e := @Continuous.measurableEmbedding
    _ _ (@borel _ t') t' _ _ (@BorelSpace.mk _ _ (borel γ) rfl)
    t _ (@borel _ t) (@BorelSpace.mk _ t (@borel _ t) rfl) (continuous_id_of_le hle) injective_id
  convert e.measurableSet_image.2 hs
  simp only [id_eq, image_id']
theorem isClopenable_iff_measurableSet
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ] :
    IsClopenable s ↔ MeasurableSet s := by
  refine ⟨fun hs => ?_, fun hs => hs.isClopenable⟩
  borelize γ
  obtain ⟨t', t't, t'_polish, _, s_open⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s := hs
  rw [← borel_eq_borel_of_le t'_polish _ t't]
  · exact MeasurableSpace.measurableSet_generateFrom s_open
  infer_instance
end
@[measurability]
lemma measurableSet_tendsto_fun [MeasurableSpace γ] [Countable ι]
    {l : Filter ι} [l.IsCountablyGenerated]
    [TopologicalSpace γ] [SecondCountableTopology γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ]
    {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) {g : β → γ} (hg : Measurable g) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) } := by
  letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric γ
  simp_rw [tendsto_iff_dist_tendsto_zero (f := fun n ↦ f n _)]
  exact measurableSet_tendsto (𝓝 0) (fun n ↦ (hf n).dist hg)
@[measurability]
theorem measurableSet_exists_tendsto [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet { x | ∃ c, Tendsto (fun n => f n x) l (𝓝 c) } := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  letI := upgradePolishSpace γ
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  simp_rw [← cauchy_map_iff_exists_tendsto]
  change MeasurableSet { x | _ ∧ _ }
  have : ∀ x, (map (f · x) l ×ˢ map (f · x) l).HasAntitoneBasis fun n =>
      ((f · x) '' u n) ×ˢ ((f · x) '' u n) := fun x => (hu.map _).prod (hu.map _)
  simp_rw [and_iff_right (hl.map _),
    Filter.HasBasis.le_basis_iff (this _).toHasBasis Metric.uniformity_basis_dist_inv_nat_succ,
    Set.setOf_forall]
  refine MeasurableSet.biInter Set.countable_univ fun K _ => ?_
  simp_rw [Set.setOf_exists, true_and]
  refine MeasurableSet.iUnion fun N => ?_
  simp_rw [prod_image_image_eq, image_subset_iff, prod_subset_iff, Set.setOf_forall]
  exact
    MeasurableSet.biInter (to_countable (u N)) fun i _ =>
      MeasurableSet.biInter (to_countable (u N)) fun j _ =>
        measurableSet_lt (Measurable.dist (hf i) (hf j)) measurable_const
end MeasureTheory
namespace StandardBorelSpace
variable [MeasurableSpace α] [StandardBorelSpace α]
theorem _root_.MeasurableSet.isClopenable' {s : Set α} (hs : MeasurableSet s) :
    ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α ∧ IsClosed s ∧ IsOpen s := by
  letI := upgradeStandardBorel α
  obtain ⟨t, hle, ht, s_clopen⟩ := hs.isClopenable
  refine ⟨t, ?_, ht, s_clopen⟩
  constructor
  rw [eq_borel_upgradeStandardBorel α, borel_eq_borel_of_le ht _ hle]
  infer_instance
theorem _root_.MeasurableSet.standardBorel {s : Set α} (hs : MeasurableSet s) :
    StandardBorelSpace s := by
  obtain ⟨_, _, _, s_closed, _⟩ := hs.isClopenable'
  haveI := s_closed.polishSpace
  infer_instance
end StandardBorelSpace
namespace PolishSpace
variable {β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [StandardBorelSpace β]
noncomputable def borelSchroederBernstein {f : α → β} {g : β → α} (fmeas : Measurable f)
    (finj : Function.Injective f) (gmeas : Measurable g) (ginj : Function.Injective g) : α ≃ᵐ β :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)
noncomputable def measurableEquivNatBoolOfNotCountable (h : ¬Countable α) : α ≃ᵐ (ℕ → Bool) := by
  apply Nonempty.some
  letI := upgradeStandardBorel α
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable (α := α)
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated α
  exact ⟨borelSchroederBernstein gmeas ginj fcts.measurable finj⟩
noncomputable def measurableEquivOfNotCountable (hα : ¬Countable α) (hβ : ¬Countable β) : α ≃ᵐ β :=
  (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm
noncomputable def Equiv.measurableEquiv (e : α ≃ β) : α ≃ᵐ β := by
  by_cases h : Countable α
  · letI := Countable.of_equiv α e
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
  refine measurableEquivOfNotCountable h ?_
  rwa [e.countable_iff] at h
end PolishSpace