import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Module.WeakDual
noncomputable section
open MeasureTheory Filter Complex Set Module
open scoped Filter Topology Real ENNReal FourierTransform RealInnerProductSpace NNReal
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}
section InnerProductSpace
variable [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
local notation3 "i" => fun (w : V) => (1 / (2 * ‖w‖ ^ 2) : ℝ) • w
theorem fourierIntegral_half_period_translate {w : V} (hw : w ≠ 0) :
    (∫ v : V, 𝐞 (-⟪v, w⟫) • f (v + i w)) = -∫ v : V, 𝐞 (-⟪v, w⟫) • f v := by
  have hiw : ⟪i w, w⟫ = 1 / 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id,
      RCLike.conj_to_real, ← div_div, div_mul_cancel₀]
    rwa [Ne, sq_eq_zero_iff, norm_eq_zero]
  have :
    (fun v : V => 𝐞 (-⟪v, w⟫) • f (v + i w)) =
      fun v : V => (fun x : V => -(𝐞 (-⟪x, w⟫) • f x)) (v + i w) := by
    ext1 v
    simp_rw [inner_add_left, hiw, Circle.smul_def, Real.fourierChar_apply, neg_add, mul_add,
      ofReal_add, add_mul, exp_add]
    have : 2 * π * -(1 / 2) = -π := by field_simp; ring
    rw [this, ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I, inv_neg, inv_one, mul_neg_one, neg_smul,
      neg_neg]
  rw [this]
  have := integral_add_right_eq_self (μ := volume) (fun (x : V) ↦ -(𝐞 (-⟪x, w⟫) • f x))
    ((fun w ↦ (1 / (2 * ‖w‖ ^ (2 : ℕ))) • w) w)
  rw [this]
  simp only [neg_smul, integral_neg]
theorem fourierIntegral_eq_half_sub_half_period_translate {w : V} (hw : w ≠ 0)
    (hf : Integrable f) :
    ∫ v : V, 𝐞 (-⟪v, w⟫) • f v = (1 / (2 : ℂ)) • ∫ v : V, 𝐞 (-⟪v, w⟫) • (f v - f (v + i w)) := by
  simp_rw [smul_sub]
  rw [integral_sub, fourierIntegral_half_period_translate hw, sub_eq_add_neg, neg_neg, ←
    two_smul ℂ _, ← @smul_assoc _ _ _ _ _ _ (IsScalarTower.left ℂ), smul_eq_mul]
  · norm_num
  exacts [(Real.fourierIntegral_convergent_iff w).2 hf,
    (Real.fourierIntegral_convergent_iff w).2 (hf.comp_add_right _)]
theorem tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun w : V => ∫ v : V, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  refine NormedAddCommGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  suffices ∃ T : ℝ, ∀ w : V, T ≤ ‖w‖ → ‖∫ v : V, 𝐞 (-⟪v, w⟫) • f v‖ < ε by
    simp_rw [← comap_dist_left_atTop_eq_cocompact (0 : V), eventually_comap, eventually_atTop,
      dist_eq_norm', sub_zero]
    exact
      let ⟨T, hT⟩ := this
      ⟨T, fun b hb v hv => hT v (hv.symm ▸ hb)⟩
  obtain ⟨R, -, hR_bd⟩ : ∃ R : ℝ, 0 < R ∧ ∀ x : V, R ≤ ‖x‖ → f x = 0 := hf2.exists_pos_le_norm
  let A := {v : V | ‖v‖ ≤ R + 1}
  have mA : MeasurableSet A := by
    suffices A = Metric.closedBall (0 : V) (R + 1) by
      rw [this]
      exact Metric.isClosed_ball.measurableSet
    simp_rw [Metric.closedBall, dist_eq_norm, sub_zero]
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ B : ℝ≥0, 0 < B ∧ volume A ≤ B := by
    have hc : IsCompact A := by
      simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using isCompact_closedBall (0 : V) _
    let B₀ := volume A
    replace hc : B₀ < ⊤ := hc.measure_lt_top
    refine ⟨B₀.toNNReal + 1, add_pos_of_nonneg_of_pos B₀.toNNReal.coe_nonneg one_pos, ?_⟩
    rw [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal hc.ne]
    exact le_self_add
  obtain ⟨δ, hδ1, hδ2⟩ :=
    Metric.uniformContinuous_iff.mp (hf2.uniformContinuous_of_continuous hf1) (ε / B)
      (div_pos hε hB_pos)
  refine ⟨1 / 2 + 1 / (2 * δ), fun w hw_bd => ?_⟩
  have hw_ne : w ≠ 0 := by
    contrapose! hw_bd; rw [hw_bd, norm_zero]
    exact add_pos one_half_pos (one_div_pos.mpr <| mul_pos two_pos hδ1)
  have hw'_nm : ‖i w‖ = 1 / (2 * ‖w‖) := by
    rw [norm_smul, norm_div, Real.norm_of_nonneg (mul_nonneg two_pos.le <| sq_nonneg _), norm_one,
      sq, ← div_div, ← div_div, ← div_div, div_mul_cancel₀ _ (norm_eq_zero.not.mpr hw_ne)]
  have : ‖(1 / 2 : ℂ)‖ = 2⁻¹ := by norm_num
  rw [fourierIntegral_eq_half_sub_half_period_translate hw_ne
      (hf1.integrable_of_hasCompactSupport hf2),
    norm_smul, this, inv_mul_eq_div, div_lt_iff₀' two_pos]
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  simp_rw [Circle.norm_smul]
  have int_A : ∫ v : V, ‖f v - f (v + i w)‖ = ∫ v in A, ‖f v - f (v + i w)‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    dsimp only [A] at hv
    simp only [mem_setOf, not_le] at hv
    rw [hR_bd v _, hR_bd (v + i w) _, sub_zero, norm_zero]
    · rw [← sub_neg_eq_add]
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [le_sub_iff_add_le, norm_neg]
      refine le_trans ?_ hv.le
      rw [add_le_add_iff_left, hw'_nm, ← div_div]
      refine (div_le_one <| norm_pos_iff.mpr hw_ne).mpr ?_
      refine le_trans (le_add_of_nonneg_right <| one_div_nonneg.mpr <| ?_) hw_bd
      exact (mul_pos (zero_lt_two' ℝ) hδ1).le
    · exact (le_add_of_nonneg_right zero_le_one).trans hv.le
  rw [int_A]; clear int_A
  have bdA : ∀ v : V, v ∈ A → ‖‖f v - f (v + i w)‖‖ ≤ ε / B := by
    simp_rw [norm_norm]
    simp_rw [dist_eq_norm] at hδ2
    refine fun x _ => (hδ2 ?_).le
    rw [sub_add_cancel_left, norm_neg, hw'_nm, ← div_div, div_lt_iff₀ (norm_pos_iff.mpr hw_ne), ←
      div_lt_iff₀' hδ1, div_div]
    exact (lt_add_of_pos_left _ one_half_pos).trans_le hw_bd
  have bdA2 := norm_setIntegral_le_of_norm_le_const (hB_vol.trans_lt ENNReal.coe_lt_top) bdA ?_
  swap
  · apply Continuous.aestronglyMeasurable
    exact continuous_norm.comp <| hf1.sub <| hf1.comp <| continuous_id'.add continuous_const
  have : ‖_‖ = ∫ v : V in A, ‖f v - f (v + i w)‖ :=
    Real.norm_of_nonneg (setIntegral_nonneg mA fun x _ => norm_nonneg _)
  rw [this] at bdA2
  refine bdA2.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (NNReal.coe_pos.mpr hB_pos), mul_comm (2 : ℝ), mul_assoc,
    mul_lt_mul_left hε]
  refine (ENNReal.toReal_mono ENNReal.coe_ne_top hB_vol).trans_lt ?_
  rw [ENNReal.coe_toReal, two_mul]
  exact lt_add_of_pos_left _ hB_pos
variable (f)
theorem tendsto_integral_exp_inner_smul_cocompact :
    Tendsto (fun w : V => ∫ v, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  by_cases hfi : Integrable f; swap
  · convert tendsto_const_nhds (x := (0 : E)) with w
    apply integral_undef
    rwa [Real.fourierIntegral_convergent_iff]
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g, hg_supp, hfg, hg_cont, -⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (div_pos hε two_pos)
  refine
    ((Metric.tendsto_nhds.mp
            (tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hg_cont
              hg_supp))
          _ (div_pos hε two_pos)).mp
      (Eventually.of_forall fun w hI => ?_)
  rw [dist_eq_norm] at hI ⊢
  have : ‖(∫ v, 𝐞 (-⟪v, w⟫) • f v) - ∫ v, 𝐞 (-⟪v, w⟫) • g v‖ ≤ ε / 2 := by
    refine le_trans ?_ hfg
    simp_rw [← integral_sub ((Real.fourierIntegral_convergent_iff w).2 hfi)
      ((Real.fourierIntegral_convergent_iff w).2 (hg_cont.integrable_of_hasCompactSupport hg_supp)),
      ← smul_sub, ← Pi.sub_apply]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 _ bilinFormOfRealInner (f - g) w
  replace := add_lt_add_of_le_of_lt this hI
  rw [add_halves] at this
  refine ((le_of_eq ?_).trans (norm_add_le _ _)).trans_lt this
  simp only [sub_zero, sub_add_cancel]
theorem Real.tendsto_integral_exp_smul_cocompact (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, 𝐞 (-(v * w)) • f v) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
theorem Real.zero_at_infty_fourierIntegral (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
theorem tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) := by
  rw [μ.isAddLeftInvariant_eq_smul volume]
  simp_rw [integral_smul_nnreal_measure]
  rw [← (smul_zero _ : Measure.addHaarScalarFactor μ volume • (0 : E) = 0)]
  apply Tendsto.const_smul
  let A := (InnerProductSpace.toDual ℝ V).symm
  have : (fun w : V →L[ℝ] ℝ ↦ ∫ v, 𝐞 (-w v) • f v) = (fun w : V ↦ ∫ v, 𝐞 (-⟪v, w⟫) • f v) ∘ A := by
    ext1 w
    congr 1 with v : 1
    rw [← inner_conj_symm, RCLike.conj_to_real, InnerProductSpace.toDual_symm_apply]
  rw [this]
  exact (tendsto_integral_exp_inner_smul_cocompact f).comp
      A.toHomeomorph.toCocompactMap.cocompact_tendsto'
end InnerProductSpace
section NoInnerProduct
variable (f) [AddCommGroup V] [TopologicalSpace V] [TopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] [Module ℝ V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
theorem tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) := by
  let V' := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have A : V ≃L[ℝ] V' := toEuclidean
  borelize V'
  let Aₘ : MeasurableEquiv V V' := A.toHomeomorph.toMeasurableEquiv
  let Adual : (V →L[ℝ] ℝ) ≃L[ℝ] V' →L[ℝ] ℝ := A.arrowCongrSL (.refl _ _)
  have : (μ.map Aₘ).IsAddHaarMeasure := A.isAddHaarMeasure_map _
  convert (tendsto_integral_exp_smul_cocompact_of_inner_product (f ∘ A.symm) (μ.map Aₘ)).comp
    Adual.toHomeomorph.toCocompactMap.cocompact_tendsto' with w
  rw [Function.comp_apply, integral_map_equiv]
  congr 1 with v : 1
  congr
  · 
    apply congr_arg w
    exact (ContinuousLinearEquiv.symm_apply_apply A v).symm
  · exact (ContinuousLinearEquiv.symm_apply_apply A v).symm
theorem Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (VectorFourier.fourierIntegral 𝐞 μ (topDualPairing ℝ V).flip f) (cocompact (V →L[ℝ] ℝ))
      (𝓝 0) :=
  _root_.tendsto_integral_exp_smul_cocompact f μ
end NoInnerProduct