import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
noncomputable section
local notation "𝕊" => Circle
open MeasureTheory Filter
open scoped Topology
namespace VectorFourier
variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
section Defs
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E)
    (w : W) : E :=
  ∫ v, e (-L v w) • f v ∂μ
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (r : ℂ) :
    fourierIntegral e μ L (r • f) = r • fourierIntegral e μ L f := by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (w : W) :
    ‖fourierIntegral e μ L f w‖ ≤ ∫ v : V, ‖f v‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]
theorem fourierIntegral_comp_add_right [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
    [μ.IsAddRightInvariant] (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (v₀ : V) :
    fourierIntegral e μ L (f ∘ fun v ↦ v + v₀) =
      fun w ↦ e (L v₀ w) • fourierIntegral e μ L f w := by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V ↦ (e (-L (v - v₀) w) : ℂ) • f v, ← integral_smul]
  congr 1 with v
  rw [← smul_assoc, smul_eq_mul, ← Circle.coe_mul, ← e.map_add_eq_mul, ← LinearMap.neg_apply,
    ← sub_eq_add_neg, ← LinearMap.sub_apply, LinearMap.map_sub, neg_sub]
end Defs
section Continuous
variable [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}
theorem fourierIntegral_convergent_iff (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (w : W) :
    Integrable (fun v : V ↦ e (-L v w) • f v) μ ↔ Integrable f μ := by
  have aux {g : V → E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V ↦ e (-L v x) • g v) μ := by
    have c : Continuous fun v ↦ e (-L v x) :=
      he.comp (hL.comp (continuous_prod_mk.mpr ⟨continuous_id, continuous_const⟩)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.smul hg.1), Circle.norm_smul]
    exact hg.norm
  refine ⟨fun hf ↦ ?_, fun hf ↦ aux hf w⟩
  have := aux hf (-w)
  simp_rw [← mul_smul (e _) (e _) (f _), ← e.map_add_eq_mul, LinearMap.map_neg, neg_add_cancel,
    e.map_zero_eq_one, one_smul] at this 
  exact this
@[deprecated (since := "2024-03-29")]
alias fourier_integral_convergent_iff := VectorFourier.fourierIntegral_convergent_iff
theorem fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {f g : V → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral e μ L (f + g) = fourierIntegral e μ L f + fourierIntegral e μ L g := by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg
theorem fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w ↦ ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w ↦ ae_of_all _ fun v ↦ le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · refine ae_of_all _ fun v ↦ (he.comp ?_).smul continuous_const
    exact (hL.comp (continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩)).neg
end Continuous
section Fubini
variable [TopologicalSpace 𝕜] [TopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}
  {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν] [SecondCountableTopology V]
variable [CompleteSpace E] [CompleteSpace F]
theorem integral_bilin_fourierIntegral_eq_flip
    {f : V → E} {g : W → F} (M : E →L[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  _ = ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν := rfl
  _ = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ := by
    rw [integral_integral_swap]
    have : Integrable (fun (p : W × V) ↦ ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
      (hg.norm.prod_mul hf.norm).const_mul _
    apply this.mono
    · 
      change AEStronglyMeasurable (fun p : W × V ↦ (M (e (-(L p.2) p.1) • f p.2) (g p.1))) _
      have A : AEStronglyMeasurable (fun (p : W × V) ↦ e (-L p.2 p.1) • f p.2) (ν.prod μ) := by
        refine (Continuous.aestronglyMeasurable ?_).smul hf.1.snd
        exact he.comp (hL.comp continuous_swap).neg
      have A' : AEStronglyMeasurable (fun p ↦ (g p.1, e (-(L p.2) p.1) • f p.2) : W × V → F × E)
        (Measure.prod ν μ) := hg.1.fst.prod_mk A
      have B : Continuous (fun q ↦ M q.2 q.1 : F × E → G) := M.flip.continuous₂
      apply B.comp_aestronglyMeasurable A' 
    · filter_upwards with ⟨ξ, x⟩
      rw [Function.uncurry_apply_pair, Submonoid.smul_def, (M.flip (g ξ)).map_smul,
        ← Submonoid.smul_def, Circle.norm_smul, ContinuousLinearMap.flip_apply,
        norm_mul, norm_norm M, norm_mul, norm_norm, norm_norm, mul_comm (‖g _‖), ← mul_assoc]
      exact M.le_opNorm₂ (f x) (g ξ)
  _ = ∫ x, (∫ ξ, M (f x) (e (-L.flip ξ x) • g ξ) ∂ν) ∂μ := by
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, LinearMap.flip_apply]
  _ = ∫ x, M (f x) (∫ ξ, e (-L.flip ξ x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    apply (fourierIntegral_convergent_iff he _ _).2 hg
    exact hL.comp continuous_swap
theorem integral_fourierIntegral_smul_eq_flip
    {f : V → ℂ} {g : W → F} (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν =
      ∫ x, (f x) • (fourierIntegral e ν L.flip g x) ∂μ :=
  integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ) he hL hf hg
end Fubini
end VectorFourier
namespace VectorFourier
variable {𝕜 ι E F V W : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →L[𝕜] W →L[𝕜] 𝕜}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
theorem fourierIntegral_continuousLinearMap_apply
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (he : Continuous e) (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₂ f w a =
      fourierIntegral e μ L.toLinearMap₂ (fun x ↦ f x a) w := by
  rw [fourierIntegral, ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂
theorem fourierIntegral_continuousMultilinearMap_apply
    {f : V → (ContinuousMultilinearMap ℝ M E)} {m : (i : ι) → M i} {w : W} (he : Continuous e)
    (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₂ f w m =
      fourierIntegral e μ L.toLinearMap₂ (fun x ↦ f x m) w := by
  rw [fourierIntegral, ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂
end VectorFourier
namespace Fourier
variable {𝕜 : Type*} [CommRing 𝕜] [MeasurableSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]
section Defs
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E :=
  VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w
theorem fourierIntegral_def (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) :
    fourierIntegral e μ f w = ∫ v : 𝕜, e (-(v * w)) • f v ∂μ :=
  rfl
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (r : ℂ) :
    fourierIntegral e μ (r • f) = r • fourierIntegral e μ f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    (f : 𝕜 → E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ ≤ ∫ x : 𝕜, ‖f x‖ ∂μ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
theorem fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    [μ.IsAddRightInvariant] (f : 𝕜 → E) (v₀ : 𝕜) :
    fourierIntegral e μ (f ∘ fun v ↦ v + v₀) = fun w ↦ e (v₀ * w) • fourierIntegral e μ f w :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _
end Defs
end Fourier
open scoped Real
namespace Real
def fourierChar : AddChar ℝ 𝕊 where
  toFun z := .exp (2 * π * z)
  map_zero_eq_one' := by simp only; rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by simp only; rw [mul_add, Circle.exp_add]
@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar
open FourierTransform
theorem fourierChar_apply (x : ℝ) : 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I) :=
  rfl
@[continuity]
theorem continuous_fourierChar : Continuous 𝐞 := Circle.exp.continuous.comp (continuous_mul_left _)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral fourierChar μ L f w =
      ∫ v : V, Complex.exp (↑(-2 * π * L v w) * Complex.I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]
@[simp]
theorem fourierIntegral_convergent_iff' {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V → E} (L : V →L[ℝ] W →L[ℝ] ℝ) (w : W) :
    Integrable (fun v : V ↦ 𝐞 (- L v w) • f v) μ ↔ Integrable f μ :=
  VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₂)
    continuous_fourierChar L.continuous₂ _
section Apply
variable {ι F V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure V} {L : V →L[ℝ] W →L[ℝ] ℝ}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
theorem fourierIntegral_continuousLinearMap_apply'
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f w a =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (fun x ↦ f x a) w :=
  VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf
theorem fourierIntegral_continuousMultilinearMap_apply'
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f w m =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (fun x ↦ f x m) w :=
  VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf
end Apply
variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  {W : Type*} [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W]
open scoped RealInnerProductSpace
@[simp] theorem fourierIntegral_convergent_iff {μ : Measure V} {f : V → E} (w : V) :
    Integrable (fun v : V ↦ 𝐞 (- ⟪v, w⟫) • f v) μ ↔ Integrable f μ :=
  fourierIntegral_convergent_iff' (innerSL ℝ) w
variable [FiniteDimensional ℝ V]
def fourierIntegral (f : V → E) (w : V) : E :=
  VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f w
def fourierIntegralInv (f : V → E) (w : V) : E :=
  VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w
@[inherit_doc] scoped[FourierTransform] notation "𝓕" => Real.fourierIntegral
@[inherit_doc] scoped[FourierTransform] notation "𝓕⁻" => Real.fourierIntegralInv
lemma fourierIntegral_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v := rfl
lemma fourierIntegral_eq' (f : V → E) (w : V) :
    𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierIntegral_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]
lemma fourierIntegralInv_eq (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v := by
  simp [fourierIntegralInv, VectorFourier.fourierIntegral]
lemma fourierIntegralInv_eq' (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierIntegralInv_eq, Circle.smul_def, Real.fourierChar_apply]
lemma fourierIntegral_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕 (f ∘ A) w = (𝓕 f) (A w) := by
  simp only [fourierIntegral_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]
lemma fourierIntegralInv_eq_fourierIntegral_neg (f : V → E) (w : V) :
    𝓕⁻ f w = 𝓕 f (-w) := by
  simp [fourierIntegral_eq, fourierIntegralInv_eq]
lemma fourierIntegralInv_eq_fourierIntegral_comp_neg (f : V → E) :
    𝓕⁻ f = 𝓕 (fun x ↦ f (-x)) := by
  ext y
  rw [fourierIntegralInv_eq_fourierIntegral_neg]
  change 𝓕 f (LinearIsometryEquiv.neg ℝ y) = 𝓕 (f ∘ LinearIsometryEquiv.neg ℝ) y
  exact (fourierIntegral_comp_linearIsometry _ _ _).symm
lemma fourierIntegralInv_comm (f : V → E) :
    𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f) := by
  conv_rhs => rw [fourierIntegralInv_eq_fourierIntegral_comp_neg]
  simp_rw [← fourierIntegralInv_eq_fourierIntegral_neg]
lemma fourierIntegralInv_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w) := by
  simp [fourierIntegralInv_eq_fourierIntegral_neg, fourierIntegral_comp_linearIsometry]
theorem fourierIntegral_real_eq (f : ℝ → E) (w : ℝ) :
    fourierIntegral f w = ∫ v : ℝ, 𝐞 (-(v * w)) • f v :=
  rfl
@[deprecated (since := "2024-02-21")] alias fourierIntegral_def := fourierIntegral_real_eq
theorem fourierIntegral_real_eq_integral_exp_smul (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourierIntegral_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]
@[deprecated (since := "2024-02-21")]
alias fourierIntegral_eq_integral_exp_smul := fourierIntegral_real_eq_integral_exp_smul
theorem fourierIntegral_continuousLinearMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → (F →L[ℝ] E)} {a : F} {v : V} (hf : Integrable f) :
    𝓕 f v a = 𝓕 (fun x ↦ f x a) v :=
  fourierIntegral_continuousLinearMap_apply' (L := innerSL ℝ) hf
theorem fourierIntegral_continuousMultilinearMap_apply {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {v : V} (hf : Integrable f) :
    𝓕 f v m = 𝓕 (fun x ↦ f x m) v :=
  fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) hf
end Real