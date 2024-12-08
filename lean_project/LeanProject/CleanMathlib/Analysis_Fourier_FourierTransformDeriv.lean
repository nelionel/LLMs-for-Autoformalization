import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Bounds
noncomputable section
open Real Complex MeasureTheory Filter TopologicalSpace
open scoped FourierTransform Topology ContDiff
attribute [local instance 101] secondCountableTopologyEither_of_left
namespace Real
lemma hasDerivAt_fourierChar (x : ℝ) : HasDerivAt (𝐞 · : ℝ → ℂ) (2 * π * I * 𝐞 x) x := by
  have h1 (y : ℝ) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x
lemma differentiable_fourierChar : Differentiable ℝ (𝐞 · : ℝ → ℂ) :=
  fun x ↦ (Real.hasDerivAt_fourierChar x).differentiableAt
lemma deriv_fourierChar (x : ℝ) : deriv (𝐞 · : ℝ → ℂ) x = 2 * π * I * 𝐞 x :=
  (Real.hasDerivAt_fourierChar x).deriv
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ)
lemma hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) :
    HasFDerivAt (fun w ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v))) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, real_smul, neg_inj]
  ring
lemma fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) :
    fderiv ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) w y = -2 * π * I * L v y * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring
lemma differentiable_fourierChar_neg_bilinear_right (v : V) :
    Differentiable ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) :=
  fun w ↦ (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt
lemma hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) :
    HasFDerivAt (fun v ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.flip w))) v :=
  hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v
lemma fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) :
    fderiv ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) v y = -2 * π * I * L y w * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul,
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring
lemma differentiable_fourierChar_neg_bilinear_left (w : W) :
    Differentiable ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) :=
  fun v ↦ (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt
end Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace VectorFourier
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)
def fourierSMulRight (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)
@[simp] lemma fourierSMulRight_apply (v : V) (w : W) :
    fourierSMulRight L f v w = -(2 * π * I) • L v w • f v := rfl
lemma hasFDerivAt_fourierChar_smul (v : V) (w : W) :
    HasFDerivAt (fun w' ↦ 𝐞 (-L v w') • f v) (𝐞 (-L v w) • fourierSMulRight L f v) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext w' : 1
  simp_rw [fourierSMulRight, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, Submonoid.smul_def, smul_eq_mul]
  push_cast
  ring_nf
lemma norm_fourierSMulRight (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := by
  rw [fourierSMulRight, norm_smul _ (ContinuousLinearMap.smulRight (L v) (f v)),
    norm_neg, norm_mul, norm_mul, norm_eq_abs I, abs_I,
    mul_one, norm_eq_abs ((_ : ℝ) : ℂ), Complex.abs_of_nonneg pi_pos.le, norm_eq_abs (2 : ℂ),
    Complex.abs_two, ContinuousLinearMap.norm_smulRight_apply, ← mul_assoc]
lemma norm_fourierSMulRight_le (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖fourierSMulRight L f v‖ ≤ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ ≤ (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] [MeasurableSpace V] [BorelSpace V]
    {L : V →L[ℝ] W →L[ℝ] ℝ} {f : V → E} {μ : Measure V}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v ↦ fourierSMulRight L f v) μ := by
  apply AEStronglyMeasurable.const_smul'
  have aux0 : Continuous fun p : (W →L[ℝ] ℝ) × E ↦ p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL ℝ W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v ↦ (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prod_mk hf
  exact (aux0.comp_aestronglyMeasurable aux1 : _)
variable {f}
theorem hasFDerivAt_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (fourierIntegral 𝐞 μ L.toLinearMap₂ f)
      (fourierIntegral 𝐞 μ L.toLinearMap₂ (fourierSMulRight L f) w) w := by
  let F : W → V → E := fun w' v ↦ 𝐞 (-L v w') • f v
  let F' : W → V → W →L[ℝ] E := fun w' v ↦ 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V → ℝ := fun v ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (fourierIntegral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₂ p.1 p.2)) w').2 hf
  have h1 : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    Eventually.of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    exact (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
  have h4 : (∀ᵐ v ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v) := by
    filter_upwards with v w' _
    rw [Circle.norm_smul _ (fourierSMulRight L f v)]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ v ∂μ, ∀ w', w' ∈ Metric.ball w 1 → HasFDerivAt (fun x ↦ F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ ↦ hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le one_pos h1 (h0 w) h3 h4 h5 h6
lemma fderiv_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) :
    fderiv ℝ (fourierIntegral 𝐞 μ L.toLinearMap₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₂ (fourierSMulRight L f) := by
  ext w : 1
  exact (hasFDerivAt_fourierIntegral L hf hf' w).fderiv
lemma differentiable_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) :
    Differentiable ℝ (fourierIntegral 𝐞 μ L.toLinearMap₂ f) :=
  fun w ↦ (hasFDerivAt_fourierIntegral L hf hf' w).differentiableAt
theorem fourierIntegral_fderiv [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ]
    (hf : Integrable f μ) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f) μ) :
    fourierIntegral 𝐞 μ L.toLinearMap₂ (fderiv ℝ f)
      = fourierSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₂ f) := by
  ext w y
  let g (v : V) : ℂ := 𝐞 (-L v w)
  suffices ∫ x, g x • fderiv ℝ f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    rw [fourierIntegral_continuousLinearMap_apply' hf']
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₂_apply, fourierSMulRight_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply, ← integral_smul, neg_smul,
      smul_neg, ← smul_smul, coe_smul, neg_neg]
  have A x : fderiv ℝ g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, ← integral_neg]
  · congr with x
    simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x ↦ (-(2 * ↑π * I * ↑((L y) w)) • ((g x : ℂ) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert this using 2 with x
    simp only [A, neg_mul, neg_smul, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact differentiable_fourierChar_neg_bilinear_left _ _
  · exact h'f
def fourierPowSMulRight (f : V → E) (v : V) : FormalMultilinearSeries ℝ W E := fun n ↦
  (- (2 * π * I))^n • ((ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (f v)).compContinuousLinearMap
  (fun _ ↦ L v))
@[simp 1100] lemma fourierPowSMulRight_apply {f : V → E} {v : V} {n : ℕ} {m : Fin n → W} :
    fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v := by
  simp [fourierPowSMulRight]
open ContinuousMultilinearMap
lemma fourierPowSMulRight_eq_comp {f : V → E} {v : V} {n : ℕ} :
    fourierPowSMulRight L f v n = (- (2 * π * I))^n • smulRightL ℝ (fun (_ : Fin n) ↦ W) E
      (compContinuousLinearMapLRight
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ) (fun _ ↦ L v)) (f v) := rfl
@[continuity, fun_prop]
lemma _root_.Continuous.fourierPowSMulRight {f : V → E} (hf : Continuous f) (n : ℕ) :
    Continuous (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ ↦ L.continuous))
lemma _root_.ContDiff.fourierPowSMulRight
    {f : V → E} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ k (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ ↦ L.contDiff)
lemma norm_fourierPowSMulRight_le (f : V → E) (v : V) (n : ℕ) :
    ‖fourierPowSMulRight L f v n‖ ≤ (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m ↦ ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [_root_.abs_of_nonneg pi_nonneg, norm_smul]
  _ ≤ (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring
set_option maxSynthPendingDepth 2 in
lemma norm_iteratedFDeriv_fourierPowSMulRight
    {f : V → E} {K : WithTop ℕ∞} {C : ℝ} (hf : ContDiff ℝ K f) {n : ℕ} {k : ℕ} (hk : k ≤ K)
    {v : V} (hv : ∀ i ≤ k, ∀ j ≤ n, ‖v‖ ^ j * ‖iteratedFDeriv ℝ i f v‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun v ↦ fourierPowSMulRight L f v n) v‖ ≤
      (2 * π) ^ n * (2 * n + 2) ^ k * ‖L‖ ^ n * C := by
  simp_rw [fourierPowSMulRight_eq_comp]
  let T : (W →L[ℝ] ℝ) [×n]→L[ℝ] (W [×n]→L[ℝ] ℝ) :=
    compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ)
  have I₁ m : ‖iteratedFDeriv ℝ m T (fun _ ↦ L v)‖ ≤
      n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m) := by
    have : ‖T‖ ≤ 1 := by
      apply (norm_compContinuousLinearMapLRight_le _ _).trans
      simp only [norm_mkPiAlgebra, le_refl]
    apply (ContinuousMultilinearMap.norm_iteratedFDeriv_le _ _ _).trans
    simp only [Fintype.card_fin]
    gcongr
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun _ ↦ ?_)
    exact ContinuousLinearMap.le_opNorm _ _
  have I₂ m : ‖iteratedFDeriv ℝ m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))) v‖ ≤
      (n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m)) * ‖L‖ ^ m := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (ContinuousMultilinearMap.contDiff _)
      _ (mod_cast le_top)]
    apply (norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    · exact I₁ m
    · exact ContinuousLinearMap.norm_pi_le_of_le (fun _ ↦ le_rfl) (norm_nonneg _)
  have I₃ m : ‖iteratedFDeriv ℝ m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))) v‖ ≤
      n.descFactorial m * ‖L‖ ^ n * ‖v‖ ^ (n - m) := by
    apply (I₂ m).trans (le_of_eq _)
    rcases le_or_lt m n with hm | hm
    · rw [show ‖L‖ ^ n = ‖L‖ ^ (m + (n - m)) by rw [Nat.add_sub_cancel' hm], pow_add]
      ring
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hm, CharP.cast_eq_zero, mul_one, zero_mul]
  have A : ContDiff ℝ K (fun y ↦ T (fun _ ↦ L y)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ ↦ L.contDiff)
  rw [iteratedFDeriv_const_smul_apply' (hf := (smulRightL ℝ (fun _ ↦ W)
    E).isBoundedBilinearMap.contDiff.comp₂ (A.of_le hk) (hf.of_le hk)),
    norm_smul (β := V [×k]→L[ℝ] (W [×n]→L[ℝ] E))]
  simp only [norm_pow, norm_neg, norm_mul, RCLike.norm_ofNat, Complex.norm_eq_abs, abs_ofReal,
    _root_.abs_of_nonneg pi_nonneg, abs_I, mul_one, mul_assoc]
  gcongr
  apply (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ A hf _
    hk ContinuousMultilinearMap.norm_smulRightL_le).trans
  calc
  ∑ i in Finset.range (k + 1),
    k.choose i * ‖iteratedFDeriv ℝ i (fun (y : V) ↦ T (fun _ ↦ L y)) v‖ *
      ‖iteratedFDeriv ℝ (k - i) f v‖
    ≤ ∑ i in Finset.range (k + 1),
      k.choose i * (n.descFactorial i * ‖L‖ ^ n * ‖v‖ ^ (n - i)) *
        ‖iteratedFDeriv ℝ (k - i) f v‖ := by
    gcongr with i _hi
    exact I₃ i
  _ = ∑ i in Finset.range (k + 1), (k.choose i * n.descFactorial i * ‖L‖ ^ n) *
        (‖v‖ ^ (n - i) * ‖iteratedFDeriv ℝ (k - i) f v‖) := by
    congr with i
    ring
  _ ≤ ∑ i in Finset.range (k + 1), (k.choose i * (n + 1 : ℕ) ^ k * ‖L‖ ^ n) * C := by
    gcongr with i hi
    · rw [← Nat.cast_pow, Nat.cast_le]
      calc n.descFactorial i ≤ n ^ i := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ i := by gcongr; omega
      _ ≤ (n + 1) ^ k := by gcongr; exacts [le_add_self, Finset.mem_range_succ_iff.mp hi]
    · exact hv _ (by omega) _ (by omega)
  _ = (2 * n + 2) ^ k * (‖L‖^n * C) := by
    simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, mul_one, ← mul_assoc,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ← mul_pow, mul_add]
variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
section SecondCountableTopology
variable [SecondCountableTopology V]
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight
    (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.const_smul'
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ ↦ L.continuous))
lemma integrable_fourierPowSMulRight {n : ℕ} (hf : Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' (h'f.fourierPowSMulRight L n) ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))
lemma hasFTaylorSeriesUpTo_fourierIntegral {N : WithTop ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₂ f)
      (fun w n ↦ fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ fourierPowSMulRight L f v n) w) := by
  constructor
  · intro w
    rw [curry0_apply, Matrix.zero_empty, fourierIntegral_continuousMultilinearMap_apply'
      (integrable_fourierPowSMulRight L (hf 0 bot_le) h'f)]
    simp only [fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_smul]
  · intro n hn w
    have I₁ : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight L (hf n hn.le) h'f
    have I₂ : Integrable (fun v ↦ ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n+1) (ENat.add_one_natCast_le_withTop_of_lt hn)).const_mul
          ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul (h'f.fourierPowSMulRight L n).norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        ≤ ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v ↦ fourierPowSMulRight L f v (n + 1)) μ :=
      integrable_fourierPowSMulRight L (hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)) h'f
    have I₄ : Integrable
        (fun v ↦ fourierSMulRight L (fun v ↦ fourierPowSMulRight L f v n) v) μ := by
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' (h'f.fourierPowSMulRight L n).fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ fourierPowSMulRight L f v (n + 1)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₂
          (fourierSMulRight L fun v ↦ fourierPowSMulRight L f v n) w := by
      ext w' m
      rw [curryLeft_apply, fourierIntegral_continuousMultilinearMap_apply' I₃,
        fourierIntegral_continuousLinearMap_apply' I₄,
        fourierIntegral_continuousMultilinearMap_apply' (I₄.apply_continuousLinearMap _)]
      congr with v
      simp only [fourierPowSMulRight_apply, mul_comm, pow_succ, neg_mul, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_smul, fourierSMulRight_apply, neg_apply, smul_apply,
        smul_comm (M := ℝ) (N := ℂ) (α := E), smul_smul]
    exact E ▸ hasFDerivAt_fourierIntegral L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight L (hf n hn) h'f
lemma hasFTaylorSeriesUpTo_fourierIntegral' {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₂ f)
      (fun w n ↦ fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ fourierPowSMulRight L f v n) w) :=
  hasFTaylorSeriesUpTo_fourierIntegral _ (fun n hn ↦ hf n (mod_cast hn)) h'f
theorem contDiff_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖) μ) :
    ContDiff ℝ N (fourierIntegral 𝐞 μ L.toLinearMap₂ f) := by
  by_cases h'f : Integrable f μ
  · exact (hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f.1).contDiff
  · have : fourierIntegral 𝐞 μ L.toLinearMap₂ f = 0 := by
      ext w; simp [fourierIntegral, integral, h'f]
    simpa [this] using contDiff_const
lemma iteratedFDeriv_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (fourierIntegral 𝐞 μ L.toLinearMap₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ fourierPowSMulRight L f v n) := by
  ext w : 1
  exact ((hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f).eq_iteratedFDeriv
    (mod_cast hn) w).symm
end SecondCountableTopology
theorem fourierIntegral_iteratedFDeriv [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) μ) {n : ℕ} (hn : n ≤ N) :
    fourierIntegral 𝐞 μ L.toLinearMap₂ (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₂ f) w n) := by
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero,
      Finset.univ_eq_empty, ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply,
      Finset.prod_empty, one_smul, fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 bot_le))]
  | succ n ih =>
    ext w m
    have J : Integrable (fderiv ℝ (iteratedFDeriv ℝ n f)) μ := by
      specialize h'f (n + 1) hn
      rw [iteratedFDeriv_succ_eq_comp_left] at h'f
      exact (LinearIsometryEquiv.integrable_comp_iff _).1 h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₂ (fderiv ℝ (iteratedFDeriv ℝ n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ hn)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _)),
          ← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    have h'n : n < N := (Nat.cast_lt.mpr n.lt_succ_self).trans_le hn
    rw [fourierIntegral_fderiv _ (h'f n h'n.le)
      (hf.differentiable_iteratedFDeriv (mod_cast h'n)) J]
    simp only [ih h'n.le, fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.flip_apply, neg_smul, smul_neg, neg_neg, smul_apply,
      fourierPowSMulRight_apply, ← coe_smul (E := E), smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring
theorem fourierPowSMulRight_iteratedFDeriv_fourierIntegral [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖^k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) {w : W} :
    fourierPowSMulRight (-L.flip)
      (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w n =
    fourierIntegral 𝐞 μ L.toLinearMap₂
      (iteratedFDeriv ℝ n (fun v ↦ fourierPowSMulRight L f v k)) w := by
  rw [fourierIntegral_iteratedFDeriv (N := N) _ (hf.fourierPowSMulRight _ _) _ hn]
  · congr
    rw [iteratedFDeriv_fourierIntegral (N := K) _ _ hf.continuous.aestronglyMeasurable hk]
    intro k hk
    simpa only [norm_iteratedFDeriv_zero] using h'f k 0 hk bot_le
  · intro m hm
    have I : Integrable (fun v ↦ ∑ p in Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) μ := by
      apply integrable_finset_sum _ (fun p hp ↦ ?_)
      simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
      exact h'f _ _ ((Nat.cast_le.2 hp.1).trans hk) ((Nat.cast_le.2 hp.2).trans hm)
    apply (I.const_mul ((2 * π) ^ k * (2 * k + 2) ^ m * ‖L‖ ^ k)).mono'
      ((hf.fourierPowSMulRight L k).continuous_iteratedFDeriv (mod_cast hm)).aestronglyMeasurable
    filter_upwards with v
    refine norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hm) (fun i hi j hj ↦ ?_)
    apply Finset.single_le_sum (f := fun p ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simpa only [Finset.mem_product, Finset.mem_range_succ_iff] using ⟨hj, hi⟩
theorem norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖^k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) {w : W} :
    ‖fourierPowSMulRight (-L.flip)
      (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w n‖ ≤
    (2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k * ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := by
  rw [fourierPowSMulRight_iteratedFDeriv_fourierIntegral L hf h'f hk hn]
  apply (norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  have I p (hp : p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1)) :
      Integrable (fun v ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) μ := by
    simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
    exact h'f _ _ (le_trans (by simpa using hp.1) hk) (le_trans (by simpa using hp.2) hn)
  rw [← integral_finset_sum _ I, ← integral_mul_left]
  apply integral_mono_of_nonneg
  · filter_upwards with v using norm_nonneg _
  · exact (integrable_finset_sum _ I).const_mul _
  · filter_upwards with v
    apply norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hn) _
    intro i hi j hj
    apply Finset.single_le_sum (f := fun p ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simp only [Finset.mem_product, Finset.mem_range_succ_iff]
      exact ⟨hj, hi⟩
lemma pow_mul_norm_iteratedFDeriv_fourierIntegral_le [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖^k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) (v : V) (w : W) :
    |L v w| ^ n * ‖(iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w‖ ≤
      ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := calc
  |L v w| ^ n * ‖(iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w‖
  _ ≤ (2 * π) ^ n
      * (|L v w| ^ n * ‖iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f) w‖) := by
    apply le_mul_of_one_le_left (by positivity)
    apply one_le_pow₀
    linarith [one_le_pi_div_two]
  _ = ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w n (fun _ ↦ v)‖ := by
    simp [norm_smul, _root_.abs_of_nonneg pi_nonneg]
  _ ≤ ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₂ f)) w n‖ * ∏ _ : Fin n, ‖v‖ :=
    le_opNorm _ _
  _ ≤ ((2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ) * ‖v‖ ^ n := by
    gcongr
    · apply norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le _ hf h'f hk hn
    · simp
  _ = ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := by
    simp [mul_pow]
    ring
end VectorFourier
namespace Real
open VectorFourier
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {f : V → E}
theorem hasFDerivAt_fourierIntegral
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) (x : V) :
    HasFDerivAt (𝓕 f) (𝓕 (fourierSMulRight (innerSL ℝ) f) x) x :=
  VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ) hf_int hvf_int x
theorem fderiv_fourierIntegral
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) :
    fderiv ℝ (𝓕 f) = 𝓕 (fourierSMulRight (innerSL ℝ) f) :=
  VectorFourier.fderiv_fourierIntegral (innerSL ℝ) hf_int hvf_int
theorem differentiable_fourierIntegral
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) :
    Differentiable ℝ (𝓕 f) :=
  VectorFourier.differentiable_fourierIntegral (innerSL ℝ) hf_int hvf_int
theorem fourierIntegral_fderiv
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f)) :
    𝓕 (fderiv ℝ f) = fourierSMulRight (-innerSL ℝ) (𝓕 f) := by
  rw [← innerSL_real_flip V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL ℝ) hf h'f hf'
theorem contDiff_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖)) :
    ContDiff ℝ N (𝓕 f) :=
  VectorFourier.contDiff_fourierIntegral (innerSL ℝ) hf
theorem iteratedFDeriv_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖))
    (h'f : AEStronglyMeasurable f) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (𝓕 f) = 𝓕 (fun v ↦ fourierPowSMulRight (innerSL ℝ) f v n) :=
  VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ) hf h'f hn
theorem fourierIntegral_iteratedFDeriv {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f)) {n : ℕ} (hn : n ≤ N) :
    𝓕 (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n) := by
  rw [← innerSL_real_flip V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL ℝ) hf h'f hn
lemma pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖^k * ‖iteratedFDeriv ℝ n f v‖))
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) (w : V) :
    ‖w‖ ^ n * ‖iteratedFDeriv ℝ k (𝓕 f) w‖ ≤ (2 * π) ^ k * (2 * k + 2) ^ n *
      ∑ p in Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ := by
  have Z : ‖w‖ ^ n * (‖w‖ ^ n * ‖iteratedFDeriv ℝ k (𝓕 f) w‖) ≤
      ‖w‖ ^ n * ((2 * (π * ‖innerSL (E := V) ℝ‖)) ^ k * ((2 * k + 2) ^ n *
          ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
            ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂volume)) := by
    have := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (innerSL ℝ) hf h'f hk hn
      w w
    simp only [innerSL_apply _ w w, real_inner_self_eq_norm_sq w, _root_.abs_pow, abs_norm,
      mul_assoc] at this
    rwa [pow_two, mul_pow, mul_assoc] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, one_mul, mul_one, zero_add, Finset.range_one, Finset.product_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk, norm_iteratedFDeriv_zero] at Z ⊢
    apply Z.trans
    conv_rhs => rw [← mul_one π]
    gcongr
    exact norm_innerSL_le _
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hn]
    positivity
  rw [mul_le_mul_left (pow_pos (by simp [hw]) n)] at Z
  apply Z.trans
  conv_rhs => rw [← mul_one π]
  simp only [mul_assoc]
  gcongr
  exact norm_innerSL_le _
lemma hasDerivAt_fourierIntegral
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h_int : Integrable fun v ↦ fourierSMulRight L f v := by
    suffices Integrable fun v ↦ ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [fourierSMulRight, neg_smul, neg_mul, Pi.smul_apply] using this.smul (-2 * π * I)
    convert ((ContinuousLinearMap.ring_lmap_equiv_self ℝ
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
      ContinuousLinearMap.map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  rw [← VectorFourier.fourierIntegral_convergent_iff continuous_fourierChar L.continuous₂ w]
    at h_int
  convert (VectorFourier.hasFDerivAt_fourierIntegral L hf hf'' w).hasDerivAt using 1
  erw [ContinuousLinearMap.integral_apply h_int]
  simp_rw [ContinuousLinearMap.smul_apply, fourierSMulRight, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, L, ContinuousLinearMap.mul_apply', mul_one,
    ← neg_mul, mul_smul]
  rfl
theorem deriv_fourierIntegral
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) :
    deriv (𝓕 f) = 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • f x) := by
  ext x
  exact (hasDerivAt_fourierIntegral hf hf' x).deriv
theorem fourierIntegral_deriv
    {f : ℝ → E} (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x) := by
  ext x
  have I : Integrable (fun x ↦ fderiv ℝ f x) := by
    simpa only [← deriv_fderiv] using (ContinuousLinearMap.smulRightL ℝ ℝ E 1).integrable_comp hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv ℝ f) x 1 := by
    simp only [fourierIntegral_continuousLinearMap_apply I, fderiv_deriv]
  rw [this, fourierIntegral_fderiv hf h'f I]
  simp only [fourierSMulRight_apply, ContinuousLinearMap.neg_apply, innerSL_apply, smul_smul,
    RCLike.inner_apply, conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, ← coe_smul]
theorem iteratedDeriv_fourierIntegral {f : ℝ → E} {N : ℕ∞} {n : ℕ}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun x ↦ x^n • f x)) (hn : n ≤ N) :
    iteratedDeriv n (𝓕 f) = 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) ^ n • f x) := by
  ext x : 1
  have A (n : ℕ) (hn : n ≤ N) : Integrable (fun v ↦ ‖v‖^n * ‖f v‖) := by
    convert (hf n hn).norm with x
    simp [norm_smul]
  have B : AEStronglyMeasurable f := by
    convert (hf 0 (zero_le _)).1 with x
    simp
  rw [iteratedDeriv, iteratedFDeriv_fourierIntegral A B hn,
    fourierIntegral_continuousMultilinearMap_apply (integrable_fourierPowSMulRight _ (A n hn) B),
    fourierIntegral_eq, fourierIntegral_eq]
  congr with y
  suffices (-(2 * π * I)) ^ n • y ^ n • f y = (-(2 * π * I * y)) ^ n • f y by
    simpa [innerSL_apply _]
  simp only [← neg_mul, ← coe_smul, smul_smul, mul_pow, ofReal_pow, mul_assoc]
theorem fourierIntegral_iteratedDeriv {f : ℝ → E} {N : ℕ∞} {n : ℕ} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedDeriv n f)) (hn : n ≤ N) :
    𝓕 (iteratedDeriv n f) = fun (x : ℝ) ↦ (2 * π * I * x) ^ n • (𝓕 f x) := by
  ext x : 1
  have A : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  change 𝓕 (fun x ↦ iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, ← fourierIntegral_continuousMultilinearMap_apply (A n hn),
    fourierIntegral_iteratedFDeriv hf A hn]
  simp [← coe_smul, smul_smul, ← mul_pow]
end Real