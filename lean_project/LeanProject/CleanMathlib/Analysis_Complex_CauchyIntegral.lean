import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Real.Cardinality
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Complex
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I := by
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equivRealProdCLM.symm
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : ℝ × ℝ → E := f ∘ e
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fun p => (f' (e p)).comp (e : ℝ × ℝ →L[ℝ] ℂ)
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I) := by
    rintro ⟨x, y⟩
    simp only [F', ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, he₁, he₂, neg_add_eq_sub,
      neg_sub]
  set R : Set (ℝ × ℝ) := [[z.re, w.re]] ×ˢ [[w.im, z.im]]
  set t : Set (ℝ × ℝ) := e ⁻¹' s
  rw [uIcc_comm z.im] at Hc Hi; rw [min_comm z.im, max_comm z.im] at Hd
  have hR : e ⁻¹' ([[z.re, w.re]] ×ℂ [[w.im, z.im]]) = R := rfl
  have htc : ContinuousOn F R := Hc.comp e.continuousOn hR.ge
  have htd :
    ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t,
      HasFDerivAt F (F' p) p :=
    fun p hp => (Hd (e p) hp).comp p e.hasFDerivAt
  simp_rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm w.im z.im, ←
    intervalIntegral.integral_neg, ← hF']
  refine (integral2_divergence_prod_of_hasFDerivWithinAt_off_countable (fun p => -(I • F p)) F
    (fun p => -(I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
    (htc.const_smul _).neg htc (fun p hp => ((htd p hp).const_smul I).neg) htd ?_).symm
  rw [← (volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)] at Hi
  simpa only [hF'] using Hi.neg
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi
theorem integral_boundary_rect_of_differentiableOn_real (f : ℂ → E) (z w : ℂ)
    (Hd : DifferentiableOn ℝ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hi : IntegrableOn (fun z => I • fderiv ℝ f z 1 - fderiv ℝ f z I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im,
        I • fderiv ℝ f (x + y * I) 1 - fderiv ℝ f (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fderiv ℝ f) z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E) (z w : ℂ)
    (s : Set ℂ) (hs : s.Countable) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 := by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv ℂ f z).restrictScalars ℝ) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars ℝ) ?_).trans ?_ <;>
      simp [← ContinuousLinearMap.map_smul]
theorem integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
    fun _x hx => Hd.differentiableAt <| (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1
theorem integral_boundary_rect_eq_zero_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn <|
    H.mono <|
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)
theorem circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable {c : ℂ}
    {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = ∮ z in C(c, r), (z - c)⁻¹ • f z := by
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : ∃ a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : ∃ b, Real.exp b = R := ⟨Real.log R, Real.exp_log (h0.trans_le hle)⟩
  rw [Real.exp_le_exp] at hle
  suffices
    (∫ θ in (0)..2 * π, I • f (circleMap c (Real.exp b) θ)) =
      ∫ θ in (0)..2 * π, I • f (circleMap c (Real.exp a) θ) by
    simpa only [circleIntegral, add_sub_cancel_left, ofReal_exp, ← exp_add, smul_smul, ←
      div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center (Real.exp_pos _).ne'),
      circleMap_sub_center, deriv_circleMap]
  set R := [[a, b]] ×ℂ [[0, 2 * π]]
  set g : ℂ → ℂ := (c + exp ·)
  have hdg : Differentiable ℂ g := differentiable_exp.const_add _
  replace hs : (g ⁻¹' s).Countable := (hs.preimage (add_right_injective c)).preimage_cexp
  have h_maps : MapsTo g R A := by rintro z ⟨h, -⟩; simpa [g, A, dist_eq, abs_exp, hle] using h.symm
  replace hc : ContinuousOn (f ∘ g) R := hc.comp hdg.continuous.continuousOn h_maps
  replace hd : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min 0 (2 * π)) (max 0 (2 * π)) \ g ⁻¹' s,
      DifferentiableAt ℂ (f ∘ g) z := by
    refine fun z hz => (hd (g z) ⟨?_, hz.2⟩).comp z (hdg _)
    simpa [g, dist_eq, abs_exp, hle, and_comm] using hz.1.1
  simpa [g, circleMap, exp_periodic _, sub_eq_zero, ← exp_add] using
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩ _ hs hc hd
theorem circleIntegral_eq_of_differentiable_on_annulus_off_countable {c : ℂ} {r R : ℝ} (h0 : 0 < r)
    (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z :=
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
        ((continuousOn_id.sub continuousOn_const).smul hc) fun z hz =>
        (differentiableAt_id.sub_const _).smul (hd z hz))
    _ = ∮ z in C(c, r), f z := circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto {c : ℂ}
    {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ {c}))
    (hd : ∀ z ∈ (ball c R \ {c}) \ s, DifferentiableAt ℂ f z) (hy : Tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : ℂ) • y := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_le_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : ∃ δ > (0 : ℝ), ∀ z ∈ closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 Real.two_pi_pos)
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩
  have hsub : closedBall c R \ ball c r ⊆ closedBall c R \ {c} :=
    diff_subset_diff_right (singleton_subset_iff.2 <| mem_ball_self hr0)
  have hsub' : ball c R \ closedBall c r ⊆ ball c R \ {c} :=
    diff_subset_diff_right (singleton_subset_iff.2 <| mem_closedBall_self hr0.le)
  have hzne : ∀ z ∈ sphere c r, z ≠ c := fun z hz =>
    ne_of_mem_of_not_mem hz fun h => hr0.ne' <| dist_self c ▸ Eq.symm h
  calc
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y‖ =
        ‖(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y‖ := by
      congr 2
      · exact circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable hr0
          hrR hs (hc.mono hsub) fun z hz => hd z ⟨hsub' hz.1, hz.2⟩
      · simp [hr0.ne']
    _ = ‖∮ z in C(c, r), (z - c)⁻¹ • (f z - y)‖ := by
      simp only [smul_sub]
      have hc' : ContinuousOn (fun z => (z - c)⁻¹) (sphere c r) :=
        (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 <| hzne _ hz
      rw [circleIntegral.integral_sub] <;> refine (hc'.smul ?_).circleIntegrable hr0.le
      · exact hc.mono <| subset_inter
          (sphere_subset_closedBall.trans <| closedBall_subset_closedBall hrR) hzne
      · exact continuousOn_const
    _ ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => ?_
      specialize hzne z hz
      rw [mem_sphere, dist_eq_norm] at hz
      rw [norm_smul, norm_inv, hz, ← dist_eq_norm]
      refine mul_le_mul_of_nonneg_left (hδ _ ⟨?_, hzne⟩).le (inv_nonneg.2 hr0.le)
      rwa [mem_closedBall_iff_norm, hz]
    _ = ε := by field_simp [hr0.ne', Real.two_pi_pos.ne']; ac_rfl
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
    {f : ℂ → E} {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I : ℂ) • f c :=
  circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono diff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt
theorem circleIntegral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
    {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0 := by
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  calc
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
    _ = (2 * ↑π * I : ℂ) • (c - c) • f c :=
      (circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
        ((continuousOn_id.sub continuousOn_const).smul hc) fun z hz =>
        (differentiableAt_id.sub_const _).smul (hd z hz))
    _ = 0 := by rw [sub_self, zero_smul, smul_zero]
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ}
    {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ s)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : ℂ → E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : ∀ z ∈ ball (c : ℂ) R \ insert w s, DifferentiableAt ℂ F z := fun z hz =>
    (differentiableAt_dslope_of_ne (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (diff_subset_diff_right (subset_insert _ _) hz))
  have HI := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF
  have hne : ∀ z ∈ sphere c R, z ≠ w := fun z hz => ne_of_mem_of_not_mem hz (ne_of_lt hw.1)
  have hFeq : EqOn F (fun z => (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R) := fun z hz ↦
    calc
      F z = (z - w)⁻¹ • (f z - f w) := update_noteq (hne z hz) _ _
      _ = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w := smul_sub _ _ _
  have hc' : ContinuousOn (fun z => (z - w)⁻¹) (sphere c R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 <| hne z hz
  rw [← circleIntegral.integral_sub_inv_of_mem_ball hw.1, ← circleIntegral.integral_smul_const, ←
    sub_eq_zero, ← circleIntegral.integral_sub, ← circleIntegral.integral_congr hR.le hFeq, HI]
  exacts [(hc'.smul (hc.mono sphere_subset_closedBall)).circleIntegrable hR.le,
    (hc'.smul continuousOn_const).circleIntegrable hR.le]
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ}
    {c w : ℂ} {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w ∈ closure (ball c R \ s) by
    lift R to ℝ≥0 using hR.le
    have A : ContinuousAt (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
      have := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg) hR
      refine this.continuousOn.continuousAt (EMetric.isOpen_ball.mem_nhds ?_)
      rwa [Metric.emetric_ball_nnreal]
    have B : ContinuousAt f w := hc.continuousAt (closedBall_mem_nhds_of_mem hw)
    refine tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono ?_)
    intro z hz
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd,
      inv_smul_smul₀]
    simp [Real.pi_ne_zero, I_ne_zero]
  refine mem_closure_iff_nhds.2 fun t ht => ?_
  set g : ℝ → ℂ := fun x => w + ofReal x
  have : Tendsto g (𝓝 0) (𝓝 w) :=
    (continuous_const.add continuous_ofReal).tendsto' 0 w (add_zero _)
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this <| inter_mem ht <| isOpen_ball.mem_nhds hw) with
    ⟨l, u, hlu₀, hlu_sub⟩
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).Nonempty := by
    refine diff_nonempty.2 fun hsub => ?_
    have : (Ioo l u).Countable :=
      (hs.preimage ((add_right_injective w).comp ofReal_injective)).mono hsub
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this
    exact this.not_lt Cardinal.aleph0_lt_continuum
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w := by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd, smul_inv_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]
theorem _root_.DiffContOnCl.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (h : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1
theorem _root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ}
    {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w := by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [diff_empty] using fun z hz => hf.differentiableAt isOpen_ball hz
theorem _root_.DifferentiableOn.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw
theorem circleIntegral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ ball c R) {f : ℂ → ℂ} (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w := by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd
theorem hasFPowerSeriesOnBall_of_differentiable_off_countable {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R where
  r_le := le_radius_cauchyPowerSeries _ _ _
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : c + w ∈ ball c R := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_emetric_ball_zero_iff,
        NNReal.coe_lt_coe, ENNReal.coe_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      hs hw' hc hd]
    exact (hasFPowerSeriesOn_cauchy_integral
      ((hc.mono sphere_subset_closedBall).circleIntegrable R.2) hR).hasSum hw
theorem _root_.DiffContOnCl.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR
protected theorem _root_.DifferentiableOn.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR
protected theorem _root_.DifferentiableOn.analyticAt {s : Set ℂ} {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt
theorem _root_.DifferentiableOn.analyticOnNhd {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s := fun _z hz => hd.analyticAt (hs.mem_nhds hz)
theorem _root_.DifferentiableOn.analyticOn {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOn ℂ f s :=
  (hd.analyticOnNhd hs).analyticOn
protected theorem _root_.DifferentiableOn.contDiffOn {s : Set ℂ} {f : ℂ → E} {n : WithTop ℕ∞}
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) : ContDiffOn ℂ n f s :=
  (hd.analyticOnNhd hs).contDiffOn_of_completeSpace
protected theorem _root_.Differentiable.analyticAt {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  hf.differentiableOn.analyticAt univ_mem
protected theorem _root_.Differentiable.contDiff
    {f : ℂ → E} (hf : Differentiable ℂ f) {n : WithTop ℕ∞} :
    ContDiff ℂ n f :=
  contDiff_iff_contDiffAt.mpr fun z ↦ (hf.analyticAt z).contDiffAt
protected theorem _root_.Differentiable.hasFPowerSeriesOnBall {f : ℂ → E} (h : Differentiable ℂ f)
    (z : ℂ) {R : ℝ≥0} (hR : 0 < R) : HasFPowerSeriesOnBall f (cauchyPowerSeries f z R) z ∞ :=
  (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩
theorem analyticOnNhd_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun d _ zs ↦ d.analyticAt (o.mem_nhds zs)⟩
theorem analyticOn_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOn ℂ f s ↔ DifferentiableOn ℂ f s := by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o
theorem analyticOnNhd_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOnNhd ℂ f univ ↔ Differentiable ℂ f := by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ
theorem analyticOn_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOn ℂ f univ ↔ Differentiable ℂ f := by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable
theorem analyticAt_iff_eventually_differentiableAt {f : ℂ → E} {c : ℂ} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt]
    apply AnalyticAt.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd ℂ f s := by
      refine DifferentiableOn.analyticOnNhd ?_ o
      intro z m
      exact (d z m).differentiableWithinAt
    exact h _ m
end Complex