import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm
suppress_compilation
open Bornology Metric Set Real
open Filter hiding map_smul
open scoped NNReal Topology Uniformity
variable {𝕜 𝕜₂ E F Fₗ : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F)
namespace ContinuousLinearMap
section Completeness
variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]
@[simps! (config := .asFn) apply]
def ofMemClosureImageCoeBounded (f : E' → F) {s : Set (E' →SL[σ₁₂] F)} (hs : IsBounded s)
    (hf : f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) : E' →SL[σ₁₂] F := by
  refine (linearMapOfMemClosureRangeCoe f ?_).mkContinuousOfExistsBound ?_
  · refine closure_mono (image_subset_iff.2 fun g _ => ?_) hf
    exact ⟨g, rfl⟩
  · 
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨C, hC⟩
    have : ∀ x, IsClosed { g : E' → F | ‖g x‖ ≤ C * ‖x‖ } := fun x =>
      isClosed_Iic.preimage (@continuous_apply E' (fun _ => F) _ x).norm
    refine ⟨C, fun x => (this x).closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf⟩
    exact g.le_of_opNorm_le (hC _ hg) _
@[simps! (config := .asFn) apply]
def ofTendstoOfBoundedRange {α : Type*} {l : Filter α} [l.NeBot] (f : E' → F)
    (g : α → E' →SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f))
    (hg : IsBounded (Set.range g)) : E' →SL[σ₁₂] F :=
  ofMemClosureImageCoeBounded f hg <| mem_closure_of_tendsto hf <|
    Eventually.of_forall fun _ => mem_image_of_mem _ <| Set.mem_range_self _
theorem tendsto_of_tendsto_pointwise_of_cauchySeq {f : ℕ → E' →SL[σ₁₂] F} {g : E' →SL[σ₁₂] F}
    (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f) : Tendsto f atTop (𝓝 g) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  suffices ∀ n x, ‖f n x - g x‖ ≤ b n * ‖x‖ from
    tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  have : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  refine le_of_tendsto this (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
  exact (f n - f m).le_of_opNorm_le (hfb _ _ _ le_rfl hm) _
instance [CompleteSpace F] : CompleteSpace (E' →SL[σ₁₂] F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have cau : ∀ v, CauchySeq fun n => f n v := fun v => hf.map (lipschitz_apply v).uniformContinuous
  choose G hG using fun v => cauchySeq_tendsto_of_complete (cau v)
  set Glin : E' →SL[σ₁₂] F :=
    ofTendstoOfBoundedRange _ _ (tendsto_pi_nhds.mpr hG) hf.isBounded_range
  exact ⟨Glin, tendsto_of_tendsto_pointwise_of_cauchySeq (tendsto_pi_nhds.2 hG) hf⟩
theorem isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) : IsCompact (closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :=
  have : ∀ x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)
theorem isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb
theorem isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' →SL[σ₁₂] F)} (hb : IsBounded s)
    (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩
theorem isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : ∀ f : E' →SL[σ₁₂] F,
      (⇑f : E' → F) ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isCompact_image_coe_of_bounded_of_closed_image hb <|
    isClosed_image_coe_of_bounded_of_weak_closed hb hc
theorem is_weak_closed_closedBall (f₀ : E' →SL[σ₁₂] F) (r : ℝ) ⦃f : E' →SL[σ₁₂] F⦄
    (hf : ⇑f ∈ closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' closedBall f₀ r)) :
    f ∈ closedBall f₀ r := by
  have hr : 0 ≤ r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' → F | ‖g x - f₀ x‖ ≤ r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf
  exact (g - f₀).le_of_opNorm_le (mem_closedBall_iff_norm.1 hg) _
theorem isClosed_image_coe_closedBall (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsClosed (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)
theorem isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsCompact (((↑) : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall <|
    is_weak_closed_closedBall f₀ r
end Completeness
section UniformlyExtend
variable [CompleteSpace F] (e : E →L[𝕜] Fₗ) (h_dense : DenseRange e)
section
variable (h_e : IsUniformInducing e)
def extend : Fₗ →SL[σ₁₂] F :=
  have cont := (uniformContinuous_uniformly_extend h_e h_dense f.uniformContinuous).continuous
  have eq := uniformly_extend_of_ind h_e h_dense f.uniformContinuous
  { toFun := (h_e.isDenseInducing h_dense).extend f
    map_add' := by
      refine h_dense.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h_dense.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }
@[simp]
theorem extend_eq (x : E) : extend f e h_dense h_e (e x) = f x :=
  IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _
theorem extend_unique (g : Fₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous
@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)
end
section
variable {N : ℝ≥0} (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) [RingHomIsometric σ₁₂]
theorem opNorm_extend_le :
    ‖f.extend e h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing‖ ≤ N * ‖f‖ := by
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ ?_) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · exact continuous_const.mul continuous_norm
  · rw [extend_eq]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]
@[deprecated (since := "2024-02-02")] alias op_norm_extend_le := opNorm_extend_le
end
end UniformlyExtend
end ContinuousLinearMap