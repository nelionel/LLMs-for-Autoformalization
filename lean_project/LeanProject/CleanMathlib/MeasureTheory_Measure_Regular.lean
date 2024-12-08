import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology
namespace MeasureTheory
namespace Measure
def InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀ r < μ U, ∃ K, K ⊆ U ∧ p K ∧ r < μ K
namespace InnerRegularWRT
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α → Prop} {U : Set α}
  {ε : ℝ≥0∞}
theorem measure_eq_iSup (H : InnerRegularWRT μ p q) (hU : q U) :
    μ U = ⨆ (K) (_ : K ⊆ U) (_ : p K), μ K := by
  refine
    le_antisymm (le_of_forall_lt fun r hr => ?_) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr
theorem exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
    (hε : ε ≠ 0) : ∃ K, K ⊆ U ∧ p K ∧ μ U < μ K + ε := by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩
protected theorem map {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegularWRT μ pa qa) {f : α → β} (hf : AEMeasurable f μ) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K))
    (hB₂ : ∀ U, qb U → MeasurableSet U) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  exact hK.trans_le (le_map_apply_image hf _)
theorem map' {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegularWRT μ pa qa) (f : α ≃ᵐ β) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K)) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [f.map_apply U] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  rwa [f.map_apply, f.preimage_image]
theorem smul (H : InnerRegularWRT μ p q) (c : ℝ≥0∞) : InnerRegularWRT (c • μ) p q := by
  intro U hU r hr
  rw [smul_apply, H.measure_eq_iSup hU, smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using hr
theorem trans {q' : Set α → Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') :
    InnerRegularWRT μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩
theorem rfl {p : Set α → Prop} : InnerRegularWRT μ p p :=
  fun U hU _r hr ↦ ⟨U, Subset.rfl, hU, hr⟩
theorem of_imp (h : ∀ s, q s → p s) : InnerRegularWRT μ p q :=
  fun U hU _ hr ↦ ⟨U, Subset.rfl, h U hU, hr⟩
theorem mono {p' q' : Set α → Prop} (H : InnerRegularWRT μ p q)
    (h : ∀ s, q' s → q s) (h' : ∀ s, p s → p' s) : InnerRegularWRT μ p' q' :=
  of_imp h' |>.trans H |>.trans (of_imp h)
end InnerRegularWRT
variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}
section Classes
variable [TopologicalSpace α]
class OuterRegular (μ : Measure α) : Prop where
  protected outerRegular :
    ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r > μ A, ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r
class Regular (μ : Measure α) extends IsFiniteMeasureOnCompacts μ, OuterRegular μ : Prop where
  innerRegular : InnerRegularWRT μ IsCompact IsOpen
class WeaklyRegular (μ : Measure α) extends OuterRegular μ : Prop where
  protected innerRegular : InnerRegularWRT μ IsClosed IsOpen
class InnerRegular (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact MeasurableSet
class InnerRegularCompactLTTop (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)
instance (priority := 100) Regular.weaklyRegular [R1Space α] [Regular μ] :
    WeaklyRegular μ where
  innerRegular := fun _U hU r hr ↦
    let ⟨K, KU, K_comp, hK⟩ := Regular.innerRegular hU r hr
    ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
      hK.trans_le (measure_mono subset_closure)⟩
end Classes
namespace OuterRegular
variable [TopologicalSpace α]
instance zero : OuterRegular (0 : Measure α) :=
  ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩
theorem _root_.Set.exists_isOpen_lt_of_lt [OuterRegular μ] (A : Set α) (r : ℝ≥0∞) (hr : μ A < r) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < r := by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩
theorem _root_.Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] :
    μ A = ⨅ (U : Set α) (_ : A ⊆ U) (_ : IsOpen U), μ U := by
  refine le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) ?_
  refine le_of_forall_lt' fun r hr => ?_
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr
theorem _root_.Set.exists_isOpen_lt_add [OuterRegular μ] (A : Set α) (hA : μ A ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < μ A + ε :=
  A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)
theorem _root_.Set.exists_isOpen_le_add (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U ≤ μ A + ε := by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩
theorem _root_.MeasurableSet.exists_isOpen_diff_lt [OuterRegular μ] {A : Set α}
    (hA : MeasurableSet A) (hA' : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, U ⊇ A ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε := by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_diff_lt_of_lt_add hA.nullMeasurableSet hAU hA' hU
protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) (μ : Measure α) [OuterRegular μ] :
    (Measure.map f μ).OuterRegular := by
  refine ⟨fun A hA r hr => ?_⟩
  rw [map_apply f.measurable hA, ← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, ?_⟩
  rwa [map_apply f.measurable this.measurableSet, f.preimage_symm, f.preimage_image]
protected theorem smul (μ : Measure α) [OuterRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine ⟨fun A _ r hr => ?_⟩
    rw [smul_apply, A.measure_eq_iInf_isOpen, smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using hr
instance smul_nnreal (μ : Measure α) [OuterRegular μ] (c : ℝ≥0) :
    OuterRegular (c • μ) :=
  OuterRegular.smul μ coe_ne_top
lemma of_restrict [OpensMeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (h : ∀ n, OuterRegular (μ.restrict (s n))) (h' : ∀ n, IsOpen (s n)) (h'' : univ ⊆ ⋃ n, s n) :
    OuterRegular μ := by
  refine ⟨fun A hA r hr => ?_⟩
  have HA : μ A < ∞ := lt_of_lt_of_le hr le_top
  have hm : ∀ n, MeasurableSet (s n) := fun n => (h' n).measurableSet
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    ∃ A' : ℕ → Set α,
      (∀ n, MeasurableSet (A' n)) ∧
        (∀ n, A' n ⊆ s n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n := by
    refine
      ⟨fun n => A ∩ disjointed s n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        inter_subset_right.trans (disjointed_subset _ _),
        (disjoint_disjointed s).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, ?_⟩
    rw [← inter_iUnion, iUnion_disjointed, univ_subset_iff.mp h'', inter_univ]
  rcases ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right, add_comm] at hδε
  have : ∀ n, ∃ U ⊇ A n, IsOpen U ∧ μ U < μ (A n) + δ n := by
    intro n
    have H₁ : ∀ t, μ.restrict (s n) t = μ (t ∩ s n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s n) (A n) ≠ ∞ := by
      rw [H₁]
      exact ((measure_mono (inter_subset_left.trans (subset_iUnion A n))).trans_lt HA).ne
    rcases (A n).exists_isOpen_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁, H₁, inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U ∩ s n, subset_inter hAU (hAs _), hUo.inter (h' n), hU⟩
  choose U hAU hUo hU using this
  refine ⟨⋃ n, U n, iUnion_mono hAU, isOpen_iUnion hUo, ?_⟩
  calc
    μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
    _ ≤ ∑' n, (μ (A n) + δ n) := ENNReal.tsum_le_tsum fun n => (hU n).le
    _ = ∑' n, μ (A n) + ∑' n, δ n := ENNReal.tsum_add
    _ = μ (⋃ n, A n) + ∑' n, δ n := (congr_arg₂ (· + ·) (measure_iUnion hAd hAm).symm rfl)
    _ < r := hδε
lemma measure_closure_eq_of_isCompact [R1Space α] [OuterRegular μ]
    {k : Set α} (hk : IsCompact k) : μ (closure k) = μ k := by
  apply le_antisymm ?_ (measure_mono subset_closure)
  simp only [measure_eq_iInf_isOpen k, le_iInf_iff]
  intro u ku u_open
  exact measure_mono (hk.closure_subset_of_isOpen u_open ku)
end OuterRegular
protected theorem FiniteSpanningSetsIn.outerRegular
    [TopologicalSpace α] [OpensMeasurableSpace α] {μ : Measure α}
    (s : μ.FiniteSpanningSetsIn { U | IsOpen U ∧ OuterRegular (μ.restrict U) }) :
    OuterRegular μ :=
  OuterRegular.of_restrict (s := fun n ↦ s.set n) (fun n ↦ (s.set_mem n).2)
    (fun n ↦ (s.set_mem n).1) s.spanning.symm.subset
namespace InnerRegularWRT
variable {p : Set α → Prop}
lemma of_restrict {μ : Measure α} {s : ℕ → Set α}
    (h : ∀ n, InnerRegularWRT (μ.restrict (s n)) p MeasurableSet)
    (hs : univ ⊆ ⋃ n, s n) (hmono : Monotone s) : InnerRegularWRT μ p MeasurableSet := by
  intro F hF r hr
  have hBU : ⋃ n, F ∩ s n = F := by rw [← inter_iUnion, univ_subset_iff.mp hs, inter_univ]
  have : μ F = ⨆ n, μ (F ∩ s n) := by
    rw [← (monotone_const.inter hmono).measure_iUnion, hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  rw [← restrict_apply hF] at hn
  rcases h n hF _ hn with ⟨K, KF, hKp, hK⟩
  exact ⟨K, KF, hKp, hK.trans_le (restrict_apply_le _ _)⟩
lemma restrict (h : InnerRegularWRT μ p (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)) (A : Set α) :
    InnerRegularWRT (μ.restrict A) p (fun s ↦ MeasurableSet s ∧ μ.restrict A s ≠ ∞) := by
  rintro s ⟨s_meas, hs⟩ r hr
  rw [restrict_apply s_meas] at hs
  obtain ⟨K, K_subs, pK, rK⟩ : ∃ K, K ⊆ (toMeasurable μ (s ∩ A)) ∩ s ∧ p K ∧ r < μ K := by
    have : r < μ ((toMeasurable μ (s ∩ A)) ∩ s) := by
      apply hr.trans_le
      rw [restrict_apply s_meas]
      exact measure_mono <| subset_inter (subset_toMeasurable μ (s ∩ A)) inter_subset_left
    refine h ⟨(measurableSet_toMeasurable _ _).inter s_meas, ?_⟩ _ this
    apply (lt_of_le_of_lt _ hs.lt_top).ne
    rw [← measure_toMeasurable (s ∩ A)]
    exact measure_mono inter_subset_left
  refine ⟨K, K_subs.trans inter_subset_right, pK, ?_⟩
  calc
  r < μ K := rK
  _ = μ.restrict (toMeasurable μ (s ∩ A)) K := by
    rw [restrict_apply' (measurableSet_toMeasurable μ (s ∩ A))]
    congr
    apply (inter_eq_left.2 ?_).symm
    exact K_subs.trans inter_subset_left
  _ = μ.restrict (s ∩ A) K := by rwa [restrict_toMeasurable]
  _ ≤ μ.restrict A K := Measure.le_iff'.1 (restrict_mono inter_subset_right le_rfl) K
lemma restrict_of_measure_ne_top (h : InnerRegularWRT μ p (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞))
    {A : Set α} (hA : μ A ≠ ∞) :
    InnerRegularWRT (μ.restrict A) p (fun s ↦ MeasurableSet s) := by
  have : Fact (μ A < ∞) := ⟨hA.lt_top⟩
  exact (restrict h A).trans (of_imp (fun s hs ↦ ⟨hs, measure_ne_top _ _⟩))
lemma of_sigmaFinite [SigmaFinite μ] :
    InnerRegularWRT μ (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) (fun s ↦ MeasurableSet s) := by
  intro s hs r hr
  set B : ℕ → Set α := spanningSets μ
  have hBU : ⋃ n, s ∩ B n = s := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have : μ s = ⨆ n, μ (s ∩ B n) := by
    rw [← (monotone_const.inter (monotone_spanningSets μ)).measure_iUnion, hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  refine ⟨s ∩ B n, inter_subset_left, ⟨hs.inter (measurableSet_spanningSets μ n), ?_⟩, hn⟩
  exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
variable [TopologicalSpace α]
theorem measurableSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen)
    (hd : ∀ ⦃s U⦄, p s → IsOpen U → p (s \ U)) :
    InnerRegularWRT μ p fun s => MeasurableSet s ∧ μ s ≠ ∞ := by
  rintro s ⟨hs, hμs⟩ r hr
  have h0 : p ∅ := by
    have : 0 < μ univ := (bot_le.trans_lt hr).trans_le (measure_mono (subset_univ _))
    obtain ⟨K, -, hK, -⟩ : ∃ K, K ⊆ univ ∧ p K ∧ 0 < μ K := H isOpen_univ _ this
    simpa using hd hK isOpen_univ
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ ε ≠ 0, ε + ε ≤ μ s ∧ r = μ s - (ε + ε) := by
    use (μ s - r) / 2
    simp [*, hr.le, ENNReal.add_halves, ENNReal.sub_sub_cancel, le_add_right, tsub_eq_zero_iff_le]
  rcases hs.exists_isOpen_diff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases (U \ s).exists_isOpen_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := diff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ENNReal.sub_lt_of_lt_add hεs ?_⟩
  calc
    μ s ≤ μ U := μ.mono hsU
    _ < μ K + ε := hKr
    _ ≤ μ (K \ U') + μ U' + ε := add_le_add_right (tsub_le_iff_right.1 le_measure_diff) _
    _ ≤ μ (K \ U') + ε + ε := by gcongr
    _ = μ (K \ U') + (ε + ε) := add_assoc _ _ _
open Finset in
theorem weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : InnerRegularWRT μ IsClosed IsOpen) : WeaklyRegular μ := by
  have hfin : ∀ {s}, μ s ≠ ∞ := @(measure_ne_top μ)
  suffices ∀ s, MeasurableSet s → ∀ ε, ε ≠ 0 → ∃ F, F ⊆ s ∧ ∃ U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε by
    refine
      { outerRegular := fun s hs r hr => ?_
        innerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine ⟨U, hsU, hUo, ?_⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  apply MeasurableSet.induction_on_open
  · intro U hU ε hε
    rcases H.exists_subset_lt_add isClosed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, Subset.rfl, hFc, hU, hF.le, le_self_add⟩
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine
      ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.isClosed_compl,
        hFc.isOpen_compl, ?_⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurableSet, hFc.measurableSet, true_and]
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
    rcases ENNReal.exists_pos_sum_of_countable' ε0' ℕ with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    have : Tendsto (fun t => (∑ k ∈ t, μ (s k)) + ε / 2) atTop (𝓝 <| μ (⋃ n, s n) + ε / 2) := by
      rw [measure_iUnion hsd hsm]
      exact Tendsto.add ENNReal.summable.hasSum tendsto_const_nhds
    rcases (this.eventually <| lt_mem_nhds <| ENNReal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    refine
      ⟨⋃ k ∈ t, F k, iUnion_mono fun k => iUnion_subset fun _ => hFs _, ⋃ n, U n, iUnion_mono hsU,
        isClosed_biUnion_finset fun k _ => hFc k, isOpen_iUnion hUo, ht.le.trans ?_, ?_⟩
    · calc
        (∑ k ∈ t, μ (s k)) + ε / 2 ≤ ((∑ k ∈ t, μ (F k)) + ∑ k ∈ t, δ k) + ε / 2 := by
          rw [← sum_add_distrib]
          gcongr
          apply hF
        _ ≤ (∑ k ∈ t, μ (F k)) + ε / 2 + ε / 2 := by
          gcongr
          exact (ENNReal.sum_le_tsum _).trans hδε.le
        _ = μ (⋃ k ∈ t, F k) + ε := by
          rw [measure_biUnion_finset, add_assoc, ENNReal.add_halves]
          exacts [fun k _ n _ hkn => (hsd hkn).mono (hFs k) (hFs n),
            fun k _ => (hFc k).measurableSet]
    · calc
        μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_iUnion_le _
        _ ≤ ∑' n, (μ (s n) + δ n) := ENNReal.tsum_le_tsum hU
        _ = μ (⋃ n, s n) + ∑' n, δ n := by rw [measure_iUnion hsd hsm, ENNReal.tsum_add]
        _ ≤ μ (⋃ n, s n) + ε := add_le_add_left (hδε.le.trans ENNReal.half_le_self) _
theorem of_pseudoMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsClosed IsOpen := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [F_mono.measure_iUnion] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩
theorem isCompact_isClosed {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsCompact IsClosed := by
  intro F hF r hr
  set B : ℕ → Set X := compactCovering X
  have hBc : ∀ n, IsCompact (F ∩ B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F ∩ B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F ∩ B n) := by
    rw [← Monotone.measure_iUnion, hBU]
    exact monotone_const.inter monotone_accumulate
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left, hBc n, hn⟩
end InnerRegularWRT
namespace InnerRegular
variable [TopologicalSpace α]
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : MeasurableSet U)
    (μ : Measure α) [InnerRegular μ] :
    μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  InnerRegular.innerRegular.measure_eq_iSup hU
instance zero : InnerRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩
instance smul [h : InnerRegular μ] (c : ℝ≥0∞) : InnerRegular (c • μ) :=
  ⟨InnerRegularWRT.smul h.innerRegular c⟩
instance smul_nnreal [InnerRegular μ] (c : ℝ≥0) : InnerRegular (c • μ) := smul (c : ℝ≥0∞)
instance (priority := 100) [InnerRegular μ] : InnerRegularCompactLTTop μ :=
  ⟨fun _s hs r hr ↦ InnerRegular.innerRegular hs.1 r hr⟩
lemma innerRegularWRT_isClosed_isOpen [R1Space α] [OpensMeasurableSpace α] [h : InnerRegular μ] :
    InnerRegularWRT μ IsClosed IsOpen := by
  intro U hU r hr
  rcases h.innerRegular hU.measurableSet r hr with ⟨K, KU, K_comp, hK⟩
  exact ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
    hK.trans_le (measure_mono subset_closure)⟩
theorem exists_isCompact_not_null [InnerRegular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, MeasurableSet.univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
@[deprecated (since := "2024-11-19")] alias exists_compact_not_null := exists_isCompact_not_null
theorem _root_.MeasurableSet.exists_lt_isCompact [InnerRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ r < μ K :=
  InnerRegular.innerRegular hA _ hr
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegular μ] {f : α → β} (hf : Continuous f) :
    InnerRegular (Measure.map f μ) :=
  ⟨InnerRegularWRT.map h.innerRegular hf.aemeasurable (fun _s hs ↦ hf.measurable hs)
    (fun _K hK ↦ hK.image hf) (fun _s hs ↦ hs)⟩
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [InnerRegular μ] (f : α ≃ₜ β) : (Measure.map f μ).InnerRegular :=
  InnerRegular.map_of_continuous f.continuous
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    InnerRegular (Measure.map f μ) ↔ InnerRegular μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f⟩
  convert h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp
end InnerRegular
namespace InnerRegularCompactLTTop
variable [TopologicalSpace α]
theorem _root_.MeasurableSet.exists_isCompact_lt_add [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ A < μ K + ε :=
  InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε
theorem _root_.MeasurableSet.exists_isCompact_isClosed_lt_add
    [InnerRegularCompactLTTop μ] [R1Space α] [BorelSpace α]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ IsClosed K ∧ μ A < μ K + ε :=
  let ⟨K, hKA, hK, hμK⟩ := hA.exists_isCompact_lt_add h'A hε
  ⟨closure K, hK.closure_subset_measurableSet hA hKA, hK.closure, isClosed_closure,
    by rwa [hK.measure_closure]⟩
theorem _root_.MeasurableSet.exists_isCompact_diff_lt [OpensMeasurableSpace α] [T2Space α]
    [InnerRegularCompactLTTop μ]  ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_diff_lt_of_lt_add hKc.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩
theorem _root_.MeasurableSet.exists_isCompact_isClosed_diff_lt [BorelSpace α] [R1Space α]
    [InnerRegularCompactLTTop μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ IsClosed K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_isClosed_lt_add h'A hε with ⟨K, hKA, hKco, hKcl, hK⟩
  exact ⟨K, hKA, hKco, hKcl, measure_diff_lt_of_lt_add hKcl.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩
theorem _root_.MeasurableSet.exists_lt_isCompact_of_ne_top [InnerRegularCompactLTTop μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ r < μ K :=
  InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) :
    μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsCompact K), μ K :=
  InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩
instance restrict [h : InnerRegularCompactLTTop μ] (A : Set α) :
    InnerRegularCompactLTTop (μ.restrict A) :=
  ⟨InnerRegularWRT.restrict h.innerRegular A⟩
instance (priority := 50) [h : InnerRegularCompactLTTop μ] [IsFiniteMeasure μ] :
    InnerRegular μ := by
  constructor
  convert h.innerRegular with s
  simp [measure_ne_top μ s]
instance (priority := 50) [BorelSpace α] [R1Space α] [InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : WeaklyRegular μ :=
  InnerRegular.innerRegularWRT_isClosed_isOpen.weaklyRegular_of_finite _
instance (priority := 50) [BorelSpace α] [R1Space α] [h : InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : Regular μ where
  innerRegular := InnerRegularWRT.trans h.innerRegular <|
    InnerRegularWRT.of_imp (fun U hU ↦ ⟨hU.measurableSet, measure_ne_top μ U⟩)
protected lemma _root_.IsCompact.exists_isOpen_lt_of_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α}
    (hK : IsCompact K) (r : ℝ≥0∞) (hr : μ K < r) :
    ∃ U, K ⊆ U ∧ IsOpen U ∧ μ U < r := by
  rcases hK.exists_open_superset_measure_lt_top μ with ⟨V, hKV, hVo, hμV⟩
  have := Fact.mk hμV
  obtain ⟨U, hKU, hUo, hμU⟩ : ∃ U, K ⊆ U ∧ IsOpen U ∧ μ.restrict V U < r :=
    exists_isOpen_lt_of_lt K r <| (restrict_apply_le _ _).trans_lt hr
  refine ⟨U ∩ V, subset_inter hKU hKV, hUo.inter hVo, ?_⟩
  rwa [restrict_apply hUo.measurableSet] at hμU
protected lemma _root_.IsCompact.measure_eq_iInf_isOpen [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α} (hK : IsCompact K) :
    μ K = ⨅ (U : Set α) (_ : K ⊆ U) (_ : IsOpen U), μ U := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    exact fun U KU _ ↦ measure_mono KU
  · apply le_of_forall_lt'
    simpa only [iInf_lt_iff, exists_prop, exists_and_left] using hK.exists_isOpen_lt_of_lt
protected theorem _root_.IsCompact.exists_isOpen_lt_add [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {K : Set α} (hK : IsCompact K) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, K ⊆ U ∧ IsOpen U ∧ μ U < μ K + ε :=
  hK.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hK.measure_lt_top.ne hε)
protected theorem _root_.MeasurableSet.exists_isOpen_symmDiff_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_isClosed_diff_lt hμs this with ⟨K, hKs, hKco, hKcl, hμK⟩
  rcases hKco.exists_isOpen_lt_add (μ := μ) this with ⟨U, hKU, hUo, hμU⟩
  refine ⟨U, hUo, hμU.trans_le le_top, ?_⟩
  rw [← ENNReal.add_halves ε, measure_symmDiff_eq hUo.nullMeasurableSet hs.nullMeasurableSet]
  gcongr
  · calc
      μ (U \ s) ≤ μ (U \ K) := by gcongr
      _ < ε / 2 := by
        apply measure_diff_lt_of_lt_add hKcl.nullMeasurableSet hKU _ hμU
        exact ne_top_of_le_ne_top hμs (by gcongr)
  · exact lt_of_le_of_lt (by gcongr) hμK
protected theorem _root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt
    [InnerRegularCompactLTTop μ] [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  rcases hs with ⟨t, htm, hst⟩
  rcases htm.exists_isOpen_symmDiff_lt (by rwa [← measure_congr hst]) hε with ⟨U, hUo, hμU, hUs⟩
  refine ⟨U, hUo, hμU, ?_⟩
  rwa [measure_congr <| (ae_eq_refl _).symmDiff hst]
instance smul [h : InnerRegularCompactLTTop μ] (c : ℝ≥0∞) : InnerRegularCompactLTTop (c • μ) := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]
    infer_instance
  by_cases h'c : c = ∞
  · constructor
    intro s hs r hr
    simp only [h'c, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul] at hr
    by_cases h's : μ s = 0
    · simp [h's] at hr
    · simp [h'c, ENNReal.mul_eq_top, h's] at hs
  · constructor
    convert InnerRegularWRT.smul h.innerRegular c using 2 with s
    have : (c • μ) s ≠ ∞ ↔ μ s ≠ ∞ := by simp [not_iff_not, ENNReal.mul_eq_top, hc, h'c]
    simp only [this]
instance smul_nnreal [InnerRegularCompactLTTop μ] (c : ℝ≥0) :
    InnerRegularCompactLTTop (c • μ) :=
  inferInstanceAs (InnerRegularCompactLTTop ((c : ℝ≥0∞) • μ))
instance (priority := 80) [InnerRegularCompactLTTop μ] [SigmaFinite μ] : InnerRegular μ :=
  ⟨InnerRegularCompactLTTop.innerRegular.trans InnerRegularWRT.of_sigmaFinite⟩
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegularCompactLTTop μ] {f : α → β} (hf : Continuous f) :
    InnerRegularCompactLTTop (Measure.map f μ) := by
  constructor
  refine InnerRegularWRT.map h.innerRegular hf.aemeasurable ?_ (fun K hK ↦ hK.image hf) ?_
  · rintro s ⟨hs, h's⟩
    exact ⟨hf.measurable hs, by rwa [map_apply hf.measurable hs] at h's⟩
  · rintro s ⟨hs, -⟩
    exact hs
end InnerRegularCompactLTTop
namespace WeaklyRegular
variable [TopologicalSpace α]
instance zero : WeaklyRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isClosed_empty, hr⟩⟩
theorem _root_.IsOpen.exists_lt_isClosed [WeaklyRegular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ F, F ⊆ U ∧ IsClosed F ∧ r < μ F :=
  WeaklyRegular.innerRegular hU r hr
theorem _root_.IsOpen.measure_eq_iSup_isClosed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [WeaklyRegular μ] : μ U = ⨆ (F) (_ : F ⊆ U) (_ : IsClosed F), μ F :=
  WeaklyRegular.innerRegular.measure_eq_iSup hU
theorem innerRegular_measurable [WeaklyRegular μ] :
    InnerRegularWRT μ IsClosed fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  WeaklyRegular.innerRegular.measurableSet_of_isOpen (fun _ _ h₁ h₂ ↦ h₁.inter h₂.isClosed_compl)
theorem _root_.MeasurableSet.exists_isClosed_lt_add [WeaklyRegular μ] {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K, K ⊆ s ∧ IsClosed K ∧ μ s < μ K + ε :=
  innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε
theorem _root_.MeasurableSet.exists_isClosed_diff_lt [OpensMeasurableSpace α] [WeaklyRegular μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F, F ⊆ A ∧ IsClosed F ∧ μ (A \ F) < ε := by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_diff_lt_of_lt_add hFc.nullMeasurableSet hFA
    (ne_top_of_le_ne_top h'A <| measure_mono hFA) hF⟩
theorem _root_.MeasurableSet.exists_lt_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ K, K ⊆ A ∧ IsClosed K ∧ r < μ K :=
  innerRegular_measurable ⟨hA, h'A⟩ _ hr
theorem _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (_ : IsClosed K), μ K :=
  innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩
theorem restrict_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α}
    (h'A : μ A ≠ ∞) : WeaklyRegular (μ.restrict A) := by
  haveI : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) (fun V V_open r hr ↦ ?_)
  have : InnerRegularWRT (μ.restrict A) IsClosed (fun s ↦ MeasurableSet s) :=
    InnerRegularWRT.restrict_of_measure_ne_top innerRegular_measurable h'A
  exact this V_open.measurableSet r hr
instance (priority := 100) of_pseudoMetrizableSpace_of_isFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    WeaklyRegular μ :=
  (InnerRegularWRT.of_pseudoMetrizableSpace μ).weaklyRegular_of_finite μ
instance (priority := 100) of_pseudoMetrizableSpace_secondCountable_of_locallyFinite {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : WeaklyRegular μ :=
  have : OuterRegular μ := by
    refine (μ.finiteSpanningSetsInOpen'.mono' fun U hU => ?_).outerRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨InnerRegularWRT.of_pseudoMetrizableSpace μ⟩
protected theorem smul [WeaklyRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).WeaklyRegular := by
  haveI := OuterRegular.smul μ hx
  exact ⟨WeaklyRegular.innerRegular.smul x⟩
instance smul_nnreal [WeaklyRegular μ] (c : ℝ≥0) : WeaklyRegular (c • μ) :=
  WeaklyRegular.smul coe_ne_top
end WeaklyRegular
namespace Regular
variable [TopologicalSpace α]
instance zero : Regular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩
theorem _root_.IsOpen.exists_lt_isCompact [Regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < μ K :=
  Regular.innerRegular hU r hr
theorem _root_.IsOpen.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [Regular μ] : μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  Regular.innerRegular.measure_eq_iSup hU
theorem exists_isCompact_not_null [Regular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
@[deprecated (since := "2024-11-19")] alias exists_compact_not_null := exists_isCompact_not_null
instance (priority := 100) [Regular μ] : InnerRegularCompactLTTop μ :=
  ⟨Regular.innerRegular.measurableSet_of_isOpen (fun _ _ hs hU ↦ hs.diff hU)⟩
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [Regular μ] (f : α ≃ₜ β) : (Measure.map f μ).Regular := by
  haveI := OuterRegular.map f μ
  haveI := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map' f.toMeasurableEquiv
        (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous)⟩
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    Regular (Measure.map f μ) ↔ Regular μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f⟩
  convert h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp
protected theorem smul [Regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).Regular := by
  haveI := OuterRegular.smul μ hx
  haveI := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩
instance smul_nnreal [Regular μ] (c : ℝ≥0) : Regular (c • μ) := Regular.smul coe_ne_top
theorem restrict_of_measure_ne_top [R1Space α] [BorelSpace α] [Regular μ]
    {A : Set α} (h'A : μ A ≠ ∞) : Regular (μ.restrict A) := by
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  constructor
  intro V hV r hr
  have R : restrict μ A V ≠ ∞ := by
    rw [restrict_apply hV.measurableSet]
    exact ((measure_mono inter_subset_right).trans_lt h'A.lt_top).ne
  exact MeasurableSet.exists_lt_isCompact_of_ne_top hV.measurableSet R hr
end Regular
instance (priority := 100) Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : Regular μ := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact ⟨(InnerRegularWRT.isCompact_isClosed μ).trans (InnerRegularWRT.of_pseudoMetrizableSpace μ)⟩
instance (priority := 100) {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [SigmaFinite μ] : InnerRegular μ := by
  refine ⟨(InnerRegularWRT.isCompact_isClosed μ).trans ?_⟩
  refine InnerRegularWRT.of_restrict (fun n ↦ ?_) (iUnion_spanningSets μ).superset
    (monotone_spanningSets μ)
  have : Fact (μ (spanningSets μ n) < ∞) := ⟨measure_spanningSets_lt_top μ n⟩
  exact WeaklyRegular.innerRegular_measurable.trans InnerRegularWRT.of_sigmaFinite
end Measure
end MeasureTheory