import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
namespace MeasureTheory
open Set Filter Topology MeasureTheory NNReal ENNReal
variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
section UnifTight
variable {f g : ι → α → β} {p : ℝ≥0∞}
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε
theorem unifTight_iff_ennreal {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε := by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp only [zero_lt_top, le_top, implies_true, and_true, true_implies]
  use ∅; simpa only [measure_empty] using zero_ne_top
theorem unifTight_iff_real {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ .ofReal ε := by
  refine ⟨fun hut rε hrε ↦ hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε ↦ ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))
namespace UnifTight
theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ s in μ.cofinite.smallSets, ∀ i, eLpNorm (s.indicator (f i)) p μ ≤ ε := by
  by_cases hε_top : ε = ∞
  · subst hε_top; simp
  rcases hf (pos_iff_ne_zero.2 (toNNReal_ne_zero.mpr ⟨hε,hε_top⟩)) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i ↦ (coe_toNNReal hε_top) ▸ hfs i⟩
  · intro s t hst ht i
    exact (eLpNorm_mono <| norm_indicator_le_of_subset hst _).trans (ht i)
  · rwa [Measure.compl_mem_cofinite, lt_top_iff_ne_top]
protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩
protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := fun ε hε ↦ by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by measurability), fun i ↦ ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top le_top).le
  obtain ⟨s, hμs, hsm, hfs, hgs⟩ :
      ∃ s ∈ μ.cofinite, MeasurableSet s ∧
        (∀ i, eLpNorm (s.indicator (f i)) p μ ≤ η) ∧
        (∀ i, eLpNorm (s.indicator (g i)) p μ ≤ η) :=
    ((hf.eventually_cofinite_indicator hη_pos.ne').and
      (hg.eventually_cofinite_indicator hη_pos.ne')).exists_measurable_mem_of_smallSets
  refine ⟨sᶜ, ne_of_lt hμs, fun i ↦ ?_⟩
  have η_cast : ↑η.toNNReal = η := coe_toNNReal hη_top
  calc
    eLpNorm (indicator sᶜᶜ (f i + g i)) p μ
      = eLpNorm (indicator s (f i) + indicator s (g i)) p μ := by rw [compl_compl, indicator_add']
    _ ≤ ε := le_of_lt <|
      hη _ _ ((hf_meas i).indicator hsm) ((hg_meas i).indicator hsm)
        (η_cast ▸ hfs i) (η_cast ▸ hgs i)
protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf
protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg
protected theorem aeeq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, ite_not, hx]
end UnifTight
theorem unifTight_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight f p μ ↔ UnifTight g p μ :=
  ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩
theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_eLpNorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩
theorem unifTight_of_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by measurability, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
  case neg => exact ⟨∅, (by measurability), fun i => False.elim <| hι <| Nonempty.intro i⟩
  cases' hι with i
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert hfε.le
private theorem unifTight_fin (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction' n with n h
  · intro f hf
    have : Subsingleton (Fin Nat.zero) := subsingleton_fin_zero 
    exact unifTight_of_subsingleton hp_top hf
  intro f hfLp ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  let g : Fin n → α → β := fun k => f k
  have hgLp : ∀ i, Memℒp (g i) p μ := fun i => hfLp i
  obtain ⟨S, hμS, hFε⟩ := h hgLp hε
  obtain ⟨s, _, hμs, hfε⟩ :=
    (hfLp n).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
  refine ⟨s ∪ S, (by measurability), fun i => ?_⟩
  by_cases hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · rw [compl_union, ← indicator_indicator]
      apply (eLpNorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · simp only [Fin.coe_eq_castSucc, Fin.castSucc_mk, g]
  · rw [(_ : i = n)]
    · rw [compl_union, inter_comm, ← indicator_indicator]
      exact (eLpNorm_indicator_le _).trans hfε.le
    · have hi' := Fin.is_lt i
      rw [Nat.lt_succ_iff] at hi'
      rw [not_lt] at hi
      simp [← le_antisymm hi' hi]
theorem unifTight_finite [Finite ι] (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n → α → β := f ∘ hn.some.symm
  have hg : ∀ i, Memℒp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  simpa only [g, Function.comp_apply, Equiv.symm_apply_apply] using hfε (hn.some i)
end UnifTight
section VitaliConvergence
variable {μ : Measure α} {p : ℝ≥0∞} {f : ℕ → α → β} {g : α → β}
private theorem unifTight_of_tendsto_Lp_zero (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hf_tendsto : Tendsto (fun n ↦ eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifTight f p μ := fun ε hε ↦by
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ENNReal.coe_pos])
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, Memℒp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨s, hμs, fun n => ?_⟩
  by_cases hn : n < N
  · exact hFε ⟨n, hn⟩
  · exact (eLpNorm_indicator_le _).trans (hNε n (not_lt.mp hn))
private theorem unifTight_of_tendsto_Lp (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hg : Memℒp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifTight f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg
private theorem tendsto_Lp_of_tendsto_ae_of_meas (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε ≠ ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  by_cases hμ : μ = 0
  · rw [hμ]; use 0; intro n _; rw [eLpNorm_measure_zero]; exact zero_le ε
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (coe_ne_top)
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := Memℒp.exists_eLpNorm_indicator_compl_lt hp' hg' hε'.ne' 
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut.exists_measurableSet_indicator hε'.ne'
  have hmE := hmEf.union hmEg
  have hfmE := (measure_union_le Ef Eg).trans_lt (add_lt_top.mpr ⟨hμEf, hμEg⟩)
  set E : Set α := Ef ∪ Eg
  have hgE' := Memℒp.restrict E hg'
  have huiE := hui.restrict  E
  have hfgE : (∀ᵐ x ∂(μ.restrict E), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :=
    ae_restrict_of_ae hfg
  have ffmE : Fact _ := { out := hfmE }
  have hInner := tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' hf hg hgE' huiE hfgE
  rw [ENNReal.tendsto_atTop_zero] at hInner
  obtain ⟨N, hfngε⟩ := hInner (ε / 3) hε'
  use N; intro n hn
  have hmfngE : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE).aestronglyMeasurable
  have hfngEε := calc
    eLpNorm (E.indicator (f n - g)) p μ
      = eLpNorm (f n - g) p (μ.restrict E) := eLpNorm_indicator_eq_eLpNorm_restrict hmE
    _ ≤ ε / 3                            := hfngε n hn
  have hmgEc : AEStronglyMeasurable _ μ := (hg.indicator hmE.compl).aestronglyMeasurable
  have hgEcε := calc
    eLpNorm (Eᶜ.indicator g) p μ
      ≤ eLpNorm (Efᶜ.indicator (Egᶜ.indicator g)) p μ := by
        unfold E; rw [compl_union, ← indicator_indicator]
    _ ≤ eLpNorm (Egᶜ.indicator g) p μ := eLpNorm_indicator_le _
    _ ≤ ε / 3 := hgε.le
  have hmfnEc : AEStronglyMeasurable _ μ := ((hf n).indicator hmE.compl).aestronglyMeasurable
  have hfnEcε : eLpNorm (Eᶜ.indicator (f n)) p μ ≤ ε / 3 := calc
    eLpNorm (Eᶜ.indicator (f n)) p μ
      ≤ eLpNorm (Egᶜ.indicator (Efᶜ.indicator (f n))) p μ := by
        unfold E; rw [compl_union, inter_comm, ← indicator_indicator]
    _ ≤ eLpNorm (Efᶜ.indicator (f n)) p μ := eLpNorm_indicator_le _
    _ ≤ ε / 3 := hfε n
  have hmfngEc : AEStronglyMeasurable _ μ :=
    (((hf n).sub hg).indicator hmE.compl).aestronglyMeasurable
  have hfngEcε := calc
    eLpNorm (Eᶜ.indicator (f n - g)) p μ
      = eLpNorm (Eᶜ.indicator (f n) - Eᶜ.indicator g) p μ := by
        rw [(Eᶜ.indicator_sub' _ _)]
    _ ≤ eLpNorm (Eᶜ.indicator (f n)) p μ + eLpNorm (Eᶜ.indicator g) p μ := by
        apply eLpNorm_sub_le (by assumption) (by assumption) hp
    _ ≤ ε / 3 + ε / 3 := add_le_add hfnEcε hgEcε
  calc
    eLpNorm (f n - g) p μ
      = eLpNorm (Eᶜ.indicator (f n - g) + E.indicator (f n - g)) p μ := by
        congr; exact (E.indicator_compl_add_self _).symm
    _ ≤ eLpNorm (indicator Eᶜ (f n - g)) p μ + eLpNorm (indicator E (f n - g)) p μ := by
        apply eLpNorm_add_le (by assumption) (by assumption) hp
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hfngEcε hfngEε
    _ = ε := by simp only [ENNReal.add_thirds] 
private theorem ae_tendsto_ae_congr {f f' : ℕ → α → β} {g g' : α → β}
    (hff' : ∀ (n : ℕ), f n =ᵐ[μ] f' n) (hgg' : g =ᵐ[μ] g')
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)) := by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx
theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.aeeq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_mk
  have hgg' := hg'.aestronglyMeasurable.ae_eq_mk (μ := μ)
  have hg'' := hg'.ae_eq hgg'
  have haefg' := ae_tendsto_ae_congr hff' hgg' hfg
  set f' := fun n => (haef n).mk (μ := μ)
  set g' := hg'.aestronglyMeasurable.mk (μ := μ)
  have haefg (n : ℕ) : f n - g =ᵐ[μ] f' n - g' := (hff' n).sub hgg'
  have hsnfg (n : ℕ) := eLpNorm_congr_ae (p := p) (haefg n)
  apply Filter.Tendsto.congr (fun n => (hsnfg n).symm)
  exact tendsto_Lp_of_tendsto_ae_of_meas hp hp' hf hg hg'' hui' hut' haefg'
theorem tendsto_Lp_of_tendstoInMeasure (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Memℒp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => 
        let ⟨δ, hδ, hδ'⟩ := hui hε
        ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      (fun ε hε => 
        let ⟨s, hμs, hfε⟩ := hut hε
        ⟨s, hμs, fun i => hfε _⟩)
      hms'⟩
theorem tendstoInMeasure_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) where
  mp h := tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1
  mpr h := ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTight_of_tendsto_Lp hp' hf hg h⟩
end VitaliConvergence
end MeasureTheory