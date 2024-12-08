import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.Basic
import Mathlib.Probability.Kernel.Disintegration.CondCDF
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.Disintegration.CDFToKernel
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
open MeasureTheory Set Filter MeasurableSpace
open scoped ENNReal MeasureTheory Topology ProbabilityTheory
namespace ProbabilityTheory.Kernel
variable {α β γ Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountablyGenerated γ]
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
section Real
lemma isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) where
  measurable := measurable_pi_iff.mpr fun _ ↦ measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ ↦ density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    · ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    rw [fst_apply' _ _ MeasurableSet.univ]
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ ≤ fst κ)
      a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · exact fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a _ := integrable_density le_rfl a measurableSet_Iic
  setIntegral a _ hA _ := setIntegral_density le_rfl a measurableSet_Iic hA
lemma isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF
noncomputable
def condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction :=
  stieltjesOfMeasurableRat (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable
lemma isCondKernelCDF_condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)
noncomputable
def condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : Kernel (α × γ) ℝ :=
  (isCondKernelCDF_condKernelCDF κ).toKernel
instance instIsMarkovKernelCondKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelReal κ) := by
  rw [condKernelReal]
  infer_instance
lemma compProd_fst_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelReal κ = κ := by
  rw [condKernelReal, compProd_toKernel]
noncomputable
def condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] : Kernel (Unit × α) ℝ :=
  (isCondKernelCDF_condCDF (κ ())).toKernel
instance instIsMarkovKernelCondKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitReal κ) := by
  rw [condKernelUnitReal]
  infer_instance
instance condKernelUnitReal.instIsCondKernel (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    κ.IsCondKernel κ.condKernelUnitReal where
  disintegrate := by rw [condKernelUnitReal, compProd_toKernel]; ext; simp
@[deprecated disintegrate (since := "2024-07-26")]
lemma compProd_fst_condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelUnitReal κ = κ := disintegrate _ _
end Real
section BorelSnd
open Classical in
noncomputable
def borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) :
    Kernel α Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministic (fun _ ↦ x₀) measurable_const)) he
lemma borelMarkovFromReal_apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) :
    borelMarkovFromReal Ω η a
      = if η a (range (embeddingReal Ω))ᶜ = 0 then (η a).comap (embeddingReal Ω)
        else (Measure.dirac (range_nonempty (embeddingReal Ω)).choose).comap (embeddingReal Ω) := by
  classical
  rw [borelMarkovFromReal, comapRight_apply, piecewise_apply, deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl
lemma borelMarkovFromReal_apply' (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) {s : Set Ω} (hs : MeasurableSet s) :
    borelMarkovFromReal Ω η a s
      = if η a (range (embeddingReal Ω))ᶜ = 0 then η a (embeddingReal Ω '' s)
        else (embeddingReal Ω '' s).indicator 1 (range_nonempty (embeddingReal Ω)).choose := by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]
instance instIsSFiniteKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsSFiniteKernel η] :
    IsSFiniteKernel (borelMarkovFromReal Ω η) :=
  IsSFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)
instance instIsFiniteKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsFiniteKernel η] :
    IsFiniteKernel (borelMarkovFromReal Ω η) :=
  IsFiniteKernel.comapRight _ (measurableEmbedding_embeddingReal Ω)
instance instIsMarkovKernelBorelMarkovFromReal (η : Kernel α ℝ) [IsMarkovKernel η] :
    IsMarkovKernel (borelMarkovFromReal Ω η) := by
  refine IsMarkovKernel.comapRight _ (measurableEmbedding_embeddingReal Ω) (fun a ↦ ?_)
  classical
  rw [piecewise_apply]
  split_ifs with h
  · rwa [← prob_compl_eq_zero_iff (measurableEmbedding_embeddingReal Ω).measurableSet_range]
  · rw [deterministic_apply]
    simp [(range_nonempty (embeddingReal Ω)).choose_spec]
lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η
      = comapRight (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))) ⊗ₖ η)
        (MeasurableEmbedding.id.prod_mk (measurableEmbedding_embeddingReal Ω)) := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prod_mk he
  change fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) h_prod_embed
  rw [comapRight_compProd_id_prod _ _ he]
  have h_fst : fst κ' = fst κ := by
    ext a u
    unfold κ'
    rw [fst_apply, map_apply _ (by fun_prop),
      Measure.map_map measurable_fst h_prod_embed.measurable, fst_apply]
    congr
  rw [h_fst]
  ext a t ht : 2
  simp_rw [compProd_apply ht]
  refine lintegral_congr_ae ?_
  have h_ae : ∀ᵐ t ∂(fst κ a), (a, t) ∈ {p : α × β | η p (range e)ᶜ = 0} := by
    rw [← h_fst]
    have h_compProd : κ' a (univ ×ˢ range e)ᶜ = 0 := by
      unfold κ'
      rw [map_apply' _ (by fun_prop)]
      swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
      suffices Prod.map id e ⁻¹' (univ ×ˢ range e)ᶜ = ∅ by rw [this]; simp
      ext x
      simp
    rw [← hη', compProd_null] at h_compProd
    swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
    simp only [preimage_compl, mem_univ, mk_preimage_prod_right] at h_compProd
    exact h_compProd
  filter_upwards [h_ae] with a ha
  rw [borelMarkovFromReal, comapRight_apply', comapRight_apply']
  rotate_left
  · exact measurable_prod_mk_left ht
  · exact measurable_prod_mk_left ht
  classical
  rw [piecewise_apply, if_pos]
  exact ha
lemma compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
    (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prod_mk he
  have : κ = comapRight κ' h_prod_embed := by
    ext c t : 2
    unfold κ'
    rw [comapRight_apply, map_apply _ (by fun_prop), h_prod_embed.comap_map]
  conv_rhs => rw [this, ← hη']
  exact compProd_fst_borelMarkovFromReal_eq_comapRight_compProd κ η hη
end BorelSnd
section CountablyGenerated
open ProbabilityTheory.Kernel
noncomputable
def condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] : Kernel (α × γ) Ω :=
  let κ' := map κ (Prod.map (id : γ → γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')
instance instIsMarkovKernelCondKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelBorel κ) := by
  rw [condKernelBorel]
  infer_instance
instance condKernelBorel.instIsCondKernel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    κ.IsCondKernel κ.condKernelBorel where
  disintegrate := by
    rw [condKernelBorel, compProd_fst_borelMarkovFromReal _ _ (compProd_fst_condKernelReal _)]
@[deprecated disintegrate (since := "2024-07-26")]
lemma compProd_fst_condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelBorel κ = κ := disintegrate _ _
end CountablyGenerated
section Unit
variable (κ : Kernel Unit (α × Ω)) [IsFiniteKernel κ]
noncomputable
def condKernelUnitBorel : Kernel (Unit × α) Ω :=
  let κ' := map κ (Prod.map (id : α → α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')
instance instIsMarkovKernelCondKernelUnitBorel : IsMarkovKernel κ.condKernelUnitBorel := by
  rw [condKernelUnitBorel]
  infer_instance
instance condKernelUnitBorel.instIsCondKernel : κ.IsCondKernel κ.condKernelUnitBorel where
  disintegrate := by
    rw [condKernelUnitBorel, compProd_fst_borelMarkovFromReal _ _ (disintegrate _ _)]
@[deprecated disintegrate (since := "2024-07-26")]
lemma compProd_fst_condKernelUnitBorel (κ : Kernel Unit (α × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelUnitBorel κ = κ := disintegrate _ _
end Unit
section Measure
variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]
noncomputable
irreducible_def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    Kernel α Ω :=
  comap (condKernelUnitBorel (const Unit ρ)) (fun a ↦ ((), a)) measurable_prod_mk_left
lemma _root_.MeasureTheory.Measure.condKernel_apply (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ρ.condKernel a = condKernelUnitBorel (const Unit ρ) ((), a) := by
  rw [Measure.condKernel]; rfl
instance _root_.MeasureTheory.Measure.condKernel.instIsCondKernel (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] : ρ.IsCondKernel ρ.condKernel where
  disintegrate := by
    have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
      ext
      simp only [fst_apply, Measure.fst, const_apply]
    have h2 : prodMkLeft Unit (Measure.condKernel ρ) = condKernelUnitBorel (const Unit ρ) := by
      ext
      simp only [prodMkLeft_apply, Measure.condKernel_apply]
    rw [Measure.compProd, h1, h2, disintegrate]
    simp
instance _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : IsMarkovKernel ρ.condKernel := by
  rw [Measure.condKernel]
  infer_instance
@[deprecated Measure.disintegrate (since := "2024-07-24")]
lemma _root_.MeasureTheory.Measure.compProd_fst_condKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := ρ.disintegrate ρ.condKernel
set_option linter.unusedVariables false in
@[deprecated Measure.IsCondKernel.apply_of_ne_zero (since := "2024-07-24"), nolint unusedArguments]
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero_of_measurableSet
    [MeasurableSingletonClass α] {x : α} (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero _ _ hx _
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero _ _ hx _
end Measure
section Countable
variable [Countable α]
@[deprecated disintegrate (since := "2024-07-24")]
lemma compProd_fst_condKernelCountable (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelCountable (fun a ↦ (κ a).condKernel)
      (fun x y h ↦ by simp [apply_congr_of_mem_measurableAtom _ h]) = κ := disintegrate _ _
end Countable
section CountableOrCountablyGenerated
variable [h : CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ]
open Classical in
noncomputable
irreducible_def condKernel : Kernel (α × β) Ω :=
  if hα : Countable α then
    condKernelCountable (fun a ↦ (κ a).condKernel)
      fun x y h ↦ by simp [apply_congr_of_mem_measurableAtom _ h]
  else letI := h.countableOrCountablyGenerated.resolve_left hα; condKernelBorel κ
instance instIsMarkovKernelCondKernel : IsMarkovKernel (condKernel κ) := by
  rw [condKernel_def]
  split_ifs <;> infer_instance
instance condKernel.instIsCondKernel : κ.IsCondKernel κ.condKernel where
  disintegrate := by rw [condKernel_def]; split_ifs with hα <;> exact disintegrate _ _
@[deprecated Kernel.disintegrate (since := "2024-07-26")]
lemma compProd_fst_condKernel : fst κ ⊗ₖ condKernel κ = κ := κ.disintegrate κ.condKernel
end CountableOrCountablyGenerated
end ProbabilityTheory.Kernel