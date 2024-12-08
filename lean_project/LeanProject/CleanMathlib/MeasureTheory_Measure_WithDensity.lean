import Mathlib.MeasureTheory.Decomposition.Exhaustion
import Mathlib.MeasureTheory.Integral.Lebesgue
open Set hiding restrict restrict_apply
open Filter ENNReal NNReal MeasureTheory.Measure
namespace MeasureTheory
variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
noncomputable
def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _
@[simp]
theorem withDensity_apply (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs
theorem withDensity_apply_le (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f a ∂μ ≤ μ.withDensity f s := by
  let t := toMeasurable (μ.withDensity f) s
  calc
  ∫⁻ a in s, f a ∂μ ≤ ∫⁻ a in t, f a ∂μ :=
    lintegral_mono_set (subset_toMeasurable (withDensity μ f) s)
  _ = μ.withDensity f t :=
    (withDensity_apply f (measurableSet_toMeasurable (withDensity μ f) s)).symm
  _ = μ.withDensity f s := measure_toMeasurable s
theorem withDensity_apply' [SFinite μ] (f : α → ℝ≥0∞) (s : Set α) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ := by
  apply le_antisymm ?_ (withDensity_apply_le f s)
  let t := toMeasurable μ s
  calc
  μ.withDensity f s ≤ μ.withDensity f t := measure_mono (subset_toMeasurable μ s)
  _ = ∫⁻ a in t, f a ∂μ := withDensity_apply f (measurableSet_toMeasurable μ s)
  _ = ∫⁻ a in s, f a ∂μ := by congr 1; exact restrict_toMeasurable_of_sFinite s
@[simp]
lemma withDensity_zero_left (f : α → ℝ≥0∞) : (0 : Measure α).withDensity f = 0 := by
  ext s hs
  rw [withDensity_apply _ hs]
  simp
theorem withDensity_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
    μ.withDensity f = μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)
lemma withDensity_mono {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) :
    μ.withDensity f ≤ μ.withDensity g := by
  refine le_iff.2 fun s hs ↦ ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  refine setLIntegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ ↦ h_le
theorem withDensity_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.add_apply, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_add_left hf]
  simp only [Pi.add_apply]
theorem withDensity_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  simpa only [add_comm] using withDensity_add_left hg f
theorem withDensity_add_measure {m : MeasurableSpace α} (μ ν : Measure α) (f : α → ℝ≥0∞) :
    (μ + ν).withDensity f = μ.withDensity f + ν.withDensity f := by
  ext1 s hs
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]
theorem withDensity_sum {ι : Type*} {m : MeasurableSpace α} (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    (sum μ).withDensity f = sum fun n => (μ n).withDensity f := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]
theorem withDensity_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul r hf]
  simp only [Pi.smul_apply, smul_eq_mul]
theorem withDensity_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul' r f hr]
  simp only [Pi.smul_apply, smul_eq_mul]
theorem withDensity_smul_measure (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (r • μ).withDensity f = r • μ.withDensity f := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, setLIntegral_smul_measure]
theorem isFiniteMeasure_withDensity {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    IsFiniteMeasure (μ.withDensity f) :=
  { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }
theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ := by
  refine AbsolutelyContinuous.mk fun s hs₁ hs₂ => ?_
  rw [withDensity_apply _ hs₁]
  exact setLIntegral_measure_zero _ _ hs₂
@[simp]
theorem withDensity_zero : μ.withDensity 0 = 0 := by
  ext1 s hs
  simp [withDensity_apply _ hs]
@[simp]
theorem withDensity_one : μ.withDensity 1 = μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]
@[simp]
theorem withDensity_const (c : ℝ≥0∞) : μ.withDensity (fun _ ↦ c) = c • μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]
theorem withDensity_tsum {ι : Type*} [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    μ.withDensity (∑' n, f n) = sum fun n => μ.withDensity (f n) := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  exact lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)
theorem withDensity_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    μ.withDensity (s.indicator f) = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [withDensity_apply _ ht, lintegral_indicator hs, restrict_comm hs, ←
    withDensity_apply _ ht]
theorem withDensity_indicator_one {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (s.indicator 1) = μ.restrict s := by
  rw [withDensity_indicator hs, withDensity_one]
theorem withDensity_ofReal_mutuallySingular {f : α → ℝ} (hf : Measurable f) :
    (μ.withDensity fun x => ENNReal.ofReal <| f x) ⟂ₘ
      μ.withDensity fun x => ENNReal.ofReal <| -f x := by
  set S : Set α := { x | f x < 0 }
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine ⟨S, hS, ?_, ?_⟩
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_ofReal, EventuallyEq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)
theorem restrict_withDensity {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [restrict_apply ht, withDensity_apply _ ht, withDensity_apply _ (ht.inter hs),
    restrict_restrict ht]
theorem restrict_withDensity' [SFinite μ] (s : Set α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [restrict_apply ht, withDensity_apply _ ht, withDensity_apply' _ (t ∩ s),
    restrict_restrict ht]
lemma trim_withDensity {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    (μ.withDensity f).trim hm = (μ.trim hm).withDensity f := by
  refine @Measure.ext _ m _ _ (fun s hs ↦ ?_)
  rw [withDensity_apply _ hs, restrict_trim _ _ hs, lintegral_trim _ hf, trim_measurableSet_eq _ hs,
    withDensity_apply _ (hm s hs)]
lemma Measure.MutuallySingular.withDensity {ν : Measure α} {f : α → ℝ≥0∞} (h : μ ⟂ₘ ν) :
    μ.withDensity f ⟂ₘ ν :=
  MutuallySingular.mono_ac h (withDensity_absolutelyContinuous _ _) AbsolutelyContinuous.rfl
@[simp]
theorem withDensity_eq_zero_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    μ.withDensity f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [← measure_univ_eq_zero, withDensity_apply _ .univ, restrict_univ, lintegral_eq_zero_iff' hf]
alias ⟨withDensity_eq_zero, _⟩ := withDensity_eq_zero_iff
theorem withDensity_apply_eq_zero' {f : α → ℝ≥0∞} {s : Set α} (hf : AEMeasurable f μ) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x ≠ 0 } ∩ s) = 0 := by
  constructor
  · intro hs
    let t := toMeasurable (μ.withDensity f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    rw [withDensity_apply f (measurableSet_toMeasurable _ s),
      lintegral_eq_zero_iff' (AEMeasurable.restrict hf),
      EventuallyEq, ae_restrict_iff'₀, ae_iff] at A
    swap
    · simp only [measurableSet_toMeasurable, MeasurableSet.nullMeasurableSet]
    simp only [Pi.zero_apply, mem_setOf_eq, Filter.mem_mk] at A
    convert A using 2
    ext x
    simp only [and_comm, exists_prop, mem_inter_iff, mem_setOf_eq,
      mem_compl_iff, not_forall]
  · intro hs
    let t := toMeasurable μ ({ x | f x ≠ 0 } ∩ s)
    have A : s ⊆ t ∪ { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_setOf_eq, eq_self_iff_true, or_true]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply withDensity_absolutelyContinuous
      rwa [measure_toMeasurable]
    rcases hf with ⟨g, hg, hfg⟩
    have t : {x | f x = 0} =ᵐ[μ.withDensity f] {x | g x = 0} := by
      apply withDensity_absolutelyContinuous
      filter_upwards [hfg] with a ha
      rw [eq_iff_iff]
      exact ⟨fun h ↦ by rw [h] at ha; exact ha.symm,
             fun h ↦ by rw [h] at ha; exact ha⟩
    rw [measure_congr t, withDensity_congr_ae hfg]
    have M : MeasurableSet { x : α | g x = 0 } := hg (measurableSet_singleton _)
    rw [withDensity_apply _ M, lintegral_eq_zero_iff hg]
    filter_upwards [ae_restrict_mem M]
    simp only [imp_self, Pi.zero_apply, imp_true_iff]
theorem withDensity_apply_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hf : Measurable f) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x ≠ 0 } ∩ s) = 0 :=
  withDensity_apply_eq_zero' <| hf.aemeasurable
theorem ae_withDensity_iff' {p : α → Prop} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x := by
  rw [ae_iff, ae_iff, withDensity_apply_eq_zero' hf, iff_iff_eq]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, mem_setOf_eq, not_forall]
theorem ae_withDensity_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x :=
  ae_withDensity_iff' <| hf.aemeasurable
theorem ae_withDensity_iff_ae_restrict' {p : α → Prop} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ.restrict { x | f x ≠ 0 }, p x := by
  rw [ae_withDensity_iff' hf, ae_restrict_iff'₀]
  · simp only [mem_setOf]
  · rcases hf with ⟨g, hg, hfg⟩
    have nonneg_eq_ae : {x | g x ≠ 0} =ᵐ[μ] {x | f x ≠ 0} := by
      filter_upwards [hfg] with a ha
      simp only [eq_iff_iff]
      exact ⟨fun (h : g a ≠ 0) ↦ by rwa [← ha] at h,
             fun (h : f a ≠ 0) ↦ by rwa [ha] at h⟩
    exact NullMeasurableSet.congr
      (MeasurableSet.nullMeasurableSet
        <| hg (measurableSet_singleton _)).compl
      nonneg_eq_ae
theorem ae_withDensity_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ.restrict { x | f x ≠ 0 }, p x :=
  ae_withDensity_iff_ae_restrict' <| hf.aemeasurable
theorem aemeasurable_withDensity_ennreal_iff' {f : α → ℝ≥0}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ≥0∞) * g x) μ := by
  have t : ∃ f', Measurable f' ∧ f =ᵐ[μ] f' := hf
  rcases t with ⟨f', hf'_m, hf'_ae⟩
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet {x | f' x ≠ 0} := hf'_m (measurableSet_singleton _).compl
    refine ⟨fun x => f' x * g' x, hf'_m.coe_nnreal_ennreal.smul g'meas, ?_⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff' hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg', hf'_ae] with a ha h'a h_a_nonneg
      have : (f' a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h_a_nonneg
      rw [← h'a] at this ⊢
      rw [ha this]
    · rw [ae_restrict_iff' A.compl]
      filter_upwards [hf'_ae] with a ha ha_null
      have ha_null : f' a = 0 := Function.nmem_support.mp ha_null
      rw [ha_null] at ha ⊢
      rw [ha]
      simp only [ENNReal.coe_zero, zero_mul]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => ((f' x)⁻¹ : ℝ≥0∞) * g' x, hf'_m.coe_nnreal_ennreal.inv.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff' hf.coe_nnreal_ennreal]
    filter_upwards [hg', hf'_ae] with a hfga hff'a h'a
    rw [hff'a] at hfga h'a
    rw [← hfga, ← mul_assoc, ENNReal.inv_mul_cancel h'a ENNReal.coe_ne_top, one_mul]
theorem aemeasurable_withDensity_ennreal_iff {f : α → ℝ≥0} (hf : Measurable f) {g : α → ℝ≥0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ≥0∞) * g x) μ :=
  aemeasurable_withDensity_ennreal_iff' <| hf.aemeasurable
open MeasureTheory.SimpleFunc
theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (h_mf : Measurable f) :
    ∀ {g : α → ℝ≥0∞}, Measurable g → ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    simp [mul_add, *, Measurable.mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => mul_le_mul_left' (h_mono_g hmn x) _
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.mul (h_mea_g _), *]
theorem setLIntegral_withDensity_eq_setLIntegral_mul (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂μ.withDensity f = ∫⁻ x in s, (f * g) x ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul _ hf hg]
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_set_lintegral_mul := setLIntegral_withDensity_eq_setLIntegral_mul
theorem lintegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.withDensity f)) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  rw [this] at hg ⊢
  let g' := hg.mk g
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x ≠ 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq, ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x ≠ 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
lemma setLIntegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.withDensity f))
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul₀' hf.restrict]
  rw [← restrict_withDensity hs]
  exact hg.restrict
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_lintegral_mul₀' := setLIntegral_withDensity_eq_lintegral_mul₀'
theorem lintegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ :=
  lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))
lemma setLIntegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ :=
  setLIntegral_withDensity_eq_lintegral_mul₀' hf
    (hg.mono' (MeasureTheory.withDensity_absolutelyContinuous μ f)) hs
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_lintegral_mul₀ := setLIntegral_withDensity_eq_lintegral_mul₀
theorem lintegral_withDensity_le_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) : (∫⁻ a, g a ∂μ.withDensity f) ≤ ∫⁻ a, (f * g) a ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  have A : f * i ≤ f * g := fun x => mul_le_mul_left' (hi x) _
  refine le_iSup₂_of_le (f * i) (f_meas.mul i_meas) ?_
  exact le_iSup_of_le A (le_of_eq (lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas))
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  refine le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) ?_
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  refine iSup₂_le fun i i_meas => iSup_le fun hi => ?_
  have A : (fun x => (f x)⁻¹ * i x) ≤ g := by
    intro x
    dsimp
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.inv.mul i_meas) ?_)
  refine le_iSup_of_le A ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx h'x.ne, one_mul]
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable :=
  setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
    {f : α → ℝ≥0∞} {s : Set α} (hf : AEMeasurable f (μ.restrict s)) (g : α → ℝ≥0∞)
    (hs : MeasurableSet s) (h'f : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ :=
  setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
theorem setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀' (μ : Measure α) [SFinite μ]
    {f : α → ℝ≥0∞} (s : Set α) (hf : AEMeasurable f (μ.restrict s)) (g : α → ℝ≥0∞)
    (h'f : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity' s, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]
@[deprecated (since := "2024-06-29")]
alias set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀' :=
  setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀'
theorem withDensity_mul₀ {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g := by
  ext1 s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul₀ hf.restrict hg.restrict]
theorem withDensity_mul (μ : Measure α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g :=
  withDensity_mul₀ hf.aemeasurable hg.aemeasurable
lemma withDensity_inv_same_le {μ : Measure α} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (μ.withDensity f).withDensity f⁻¹ ≤ μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) ≤ μ
  rw [← withDensity_mul₀ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) ≤ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  filter_upwards with x
  simp only [Pi.mul_apply, Pi.one_apply]
  by_cases hx_top : f x = ∞
  · simp only [hx_top, ENNReal.inv_top, mul_zero, zero_le]
  by_cases hx_zero : f x = 0
  · simp only [hx_zero, ENNReal.inv_zero, zero_mul, zero_le]
  rw [ENNReal.mul_inv_cancel hx_zero hx_top]
lemma withDensity_inv_same₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ := by
  rw [← withDensity_mul₀ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this, withDensity_one]
  filter_upwards [hf_ne_zero, hf_ne_top] with x hf_ne_zero hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_ne_zero hf_ne_top, Pi.one_apply]
lemma withDensity_inv_same {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ :=
  withDensity_inv_same₀ hf.aemeasurable hf_ne_zero hf_ne_top
lemma withDensity_absolutelyContinuous' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) :
    μ ≪ μ.withDensity f := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμs ↦ ?_)
  rw [withDensity_apply _ hs, lintegral_eq_zero_iff' hf.restrict,
    ae_eq_restrict_iff_indicator_ae_eq hs, Set.indicator_zero', Filter.EventuallyEq, ae_iff] at hμs
  simp only [ae_iff, ne_eq, not_not] at hf_ne_zero
  simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, not_forall, exists_prop] at hμs
  have hle : s ⊆ {a | a ∈ s ∧ ¬f a = 0} ∪ {a | f a = 0} :=
    fun x hx ↦ or_iff_not_imp_right.mpr <| fun hnx ↦ ⟨hx, hnx⟩
  exact measure_mono_null hle <| nonpos_iff_eq_zero.1 <| le_trans (measure_union_le _ _)
    <| hμs.symm ▸ zero_add _ |>.symm ▸ hf_ne_zero.le
theorem withDensity_ae_eq {β : Type} {f g : α → β} {d : α → ℝ≥0∞}
    (hd : AEMeasurable d μ) (h_ae_nonneg : ∀ᵐ x ∂μ, d x ≠ 0) :
    f =ᵐ[μ.withDensity d] g ↔ f =ᵐ[μ] g :=
  Iff.intro
  (fun h ↦ Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous' hd h_ae_nonneg) h)
  (fun h ↦ Measure.AbsolutelyContinuous.ae_eq
    (withDensity_absolutelyContinuous μ d) h)
protected instance SigmaFinite.withDensity [SigmaFinite μ] (f : α → ℝ≥0) :
    SigmaFinite (μ.withDensity (fun x ↦ f x)) := by
  refine ⟨⟨⟨fun n ↦ spanningSets μ n ∩ f ⁻¹' (Iic n), fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · rw [withDensity_apply']
    apply setLIntegral_lt_top_of_bddAbove
    · exact ((measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)).ne
    · exact ⟨n, forall_mem_image.2 fun x hx ↦ hx.2⟩
  · rw [iUnion_eq_univ_iff]
    refine fun x ↦ ⟨max (spanningSetsIndex μ x) ⌈f x⌉₊, ?_, ?_⟩
    · exact mem_spanningSets_of_index_le _ _ (le_max_left ..)
    · simp [Nat.le_ceil]
lemma SigmaFinite.withDensity_of_ne_top [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) : SigmaFinite (μ.withDensity f) := by
  have : f =ᵐ[μ] fun x ↦ (f x).toNNReal := hf_ne_top.mono fun x hx ↦ (ENNReal.coe_toNNReal hx).symm
  rw [withDensity_congr_ae this]
  infer_instance
lemma SigmaFinite.withDensity_of_ne_top' [SigmaFinite μ] {f : α → ℝ≥0∞} (hf_ne_top : ∀ x, f x ≠ ∞) :
    SigmaFinite (μ.withDensity f) :=
  SigmaFinite.withDensity_of_ne_top <| ae_of_all _ hf_ne_top
instance SigmaFinite.withDensity_ofReal [SigmaFinite μ] (f : α → ℝ) :
    SigmaFinite (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) :=
  .withDensity _
section SFinite
variable (μ) in
theorem exists_measurable_le_withDensity_eq [SFinite μ] (f : α → ℝ≥0∞) :
    ∃ g, Measurable g ∧ g ≤ f ∧ μ.withDensity g = μ.withDensity f := by
  obtain ⟨g, hgm, hgf, hint⟩ := exists_measurable_le_forall_setLIntegral_eq μ f
  use g, hgm, hgf
  ext s hs
  simp only [hint, withDensity_apply _ hs]
instance Measure.withDensity.instSFinite [SFinite μ] {f : α → ℝ≥0∞} :
    SFinite (μ.withDensity f) := by
  wlog hfm : Measurable f generalizing f
  · rcases exists_measurable_le_withDensity_eq μ f with ⟨g, hgm, -, h⟩
    exact h ▸ this hgm
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · rw [← sum_sfiniteSeq μ, withDensity_sum]
    have (n : ℕ) : SFinite ((sfiniteSeq μ n).withDensity f) := this inferInstance
    infer_instance
  set s := {x | f x = ∞}
  have hs : MeasurableSet s := hfm (measurableSet_singleton _)
  have key := calc
    μ.withDensity f = μ.withDensity (sᶜ.indicator f) + μ.withDensity (s.indicator f) := by
      simp (disch := measurability) [withDensity_indicator, ← restrict_withDensity]
    _ = μ.withDensity (sᶜ.indicator f) + .sum fun _ : ℕ ↦ μ.withDensity (s.indicator 1) := by
      rw [← withDensity_tsum (by measurability)]
      congr 2 with x
      rw [ENNReal.tsum_apply]
      if hx : x ∈ s then simpa [hx, ENNReal.tsum_const_eq_top_of_ne_zero]
      else simp [hx]
  have : SigmaFinite (μ.withDensity (sᶜ.indicator f)) := by
    refine SigmaFinite.withDensity_of_ne_top <| ae_of_all _ fun x hx ↦ ?_
    simp [indicator_apply, ite_eq_iff, s] at hx
  have : SigmaFinite (μ.withDensity (s.indicator 1)) := by
    rw [withDensity_indicator hs]
    exact SigmaFinite.withDensity 1
  rw [key]
  infer_instance
@[deprecated Measure.withDensity.instSFinite (since := "2024-07-14"), nolint unusedArguments]
lemma sFinite_withDensity_of_sigmaFinite_of_measurable (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ≥0∞} (_hf : Measurable f) :
    SFinite (μ.withDensity f) :=
  inferInstance
@[deprecated Measure.withDensity.instSFinite (since := "2024-07-14"), nolint unusedArguments]
lemma sFinite_withDensity_of_measurable (μ : Measure α) [SFinite μ]
    {f : α → ℝ≥0∞} (_hf : Measurable f) :
    SFinite (μ.withDensity f) :=
  inferInstance
instance [SFinite μ] (c : ℝ≥0∞) : SFinite (c • μ) := by
  rw [← withDensity_const]
  infer_instance
theorem sFinite_of_absolutelyContinuous {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν) :
    SFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) measurableSet_sigmaFiniteSetWRT,
    restrict_compl_sigmaFiniteSetWRT hμν]
  infer_instance
end SFinite
variable [TopologicalSpace α] [OpensMeasurableSpace α] [IsLocallyFiniteMeasure μ]
lemma IsLocallyFiniteMeasure.withDensity_coe {f : α → ℝ≥0} (hf : Continuous f) :
    IsLocallyFiniteMeasure (μ.withDensity fun x ↦ f x) := by
  refine ⟨fun x ↦ ?_⟩
  rcases (μ.finiteAt_nhds x).exists_mem_basis ((nhds_basis_opens' x).restrict_subset
    ((hf.tendsto x).eventually_le_const (lt_add_one _))) with ⟨U, ⟨⟨hUx, hUo⟩, hUf⟩, hμU⟩
  refine ⟨U, hUx, ?_⟩
  rw [withDensity_apply _ hUo.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hμU.ne ⟨f x + 1, forall_mem_image.2 hUf⟩
lemma IsLocallyFiniteMeasure.withDensity_ofReal {f : α → ℝ} (hf : Continuous f) :
    IsLocallyFiniteMeasure (μ.withDensity fun x ↦ .ofReal (f x)) :=
  .withDensity_coe <| continuous_real_toNNReal.comp hf
end MeasureTheory