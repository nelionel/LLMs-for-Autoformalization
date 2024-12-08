import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Slope
open Metric Set Asymptotics ContinuousLinearMap Filter
open scoped Topology NNReal
theorem MonotoneOn.convexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn ℝ D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
      have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
        exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y) :=
        exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)
theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine ⟨b, ⟨hxa.trans hab, hby⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab
theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · push_neg at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨b, ⟨hxw.trans hwb, hby⟩, ?_⟩
    simp only [div_lt_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine ⟨b, ⟨hxb, hba.trans hay⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba
theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · push_neg at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨a, ⟨hxa, haw.trans hwy⟩, ?_⟩
    simp only [lt_div_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
    have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a :=
      StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y) :=
      StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'
lemma convexOn_of_hasDerivWithinAt2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 ≤ f'' x) : ConvexOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx using 1
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]
lemma concaveOn_of_hasDerivWithinAt2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, f'' x ≤ 0) : ConcaveOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx using 1
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]
theorem strictConvexOn_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, 0 < (deriv^[2] f) x) :
    StrictConvexOn ℝ D f :=
  ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf
theorem strictConcaveOn_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, deriv^[2] f x < 0) :
    StrictConcaveOn ℝ D f :=
  ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, deriv^[2] f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, deriv^[2] f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x
section slope
variable {𝕜 : Type*} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}
lemma ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) : MonotoneOn (slope f x) (s \ {x}) :=
  (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' ↦ hfc.secant_mono hx (mem_of_mem_diff hy)
    (mem_of_mem_diff hz) (not_mem_of_mem_diff hy :) (not_mem_of_mem_diff hz :) hz'
lemma ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x ∈ s) :
    AntitoneOn (slope f x) (s \ {x}) := by
  rw [← neg_neg f, slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg
end slope
namespace ConvexOn
variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
section left
lemma le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' ≤ slope f x y := by
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' not_mem_Ioi_self).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t ∈ S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩
lemma right_deriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt
lemma le_slope_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S x) :
    f' ≤ slope f x y := by
  refine hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy (hf'.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Ioi_iff_exists_Ioc_subset]
  exact ⟨y, hxy, Ioc_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma derivWithin_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt
lemma le_slope_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (ha : HasDerivAt f f' x) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt
lemma deriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x ≤ slope f x y :=
  le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt
end left
section right
lemma slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y ≤ f' := by
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' not_mem_Iio_self).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t ∈ S) hxy.ne ht'.ne ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩
lemma slope_le_left_deriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y ≤ derivWithin f (Iio y) y :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
lemma slope_le_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    slope f x y ≤ f' := by
  refine hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy (hf'.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Iio_iff_exists_Ico_subset]
  exact ⟨x, hxy, Ico_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma slope_le_derivWithin (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y ≤ derivWithin f S y :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma slope_le_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
lemma slope_le_deriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y ≤ deriv f y :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end right
lemma monotoneOn_derivWithin (hfc : ConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    MonotoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))
theorem monotoneOn_deriv (hfc : ConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))
end ConvexOn
namespace StrictConvexOn
variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
section left
lemma lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' < slope f x y := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt this
lemma right_deriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) :
    f' < slope f x y := by
  refine hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy (hf'.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Ioi_iff_exists_Ioc_subset]
  exact ⟨y, hxy, Ioc_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma derivWithin_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma lt_slope_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt
lemma deriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end left
section right
lemma slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y)  :
    slope f x y < f' := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
  exact this.trans_le <| hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu hy huy hf'
lemma slope_lt_left_deriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y)  :
    slope f x y < derivWithin f (Iio y) y :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    slope f x y < f' := by
  refine hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy (hf'.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Iio_iff_exists_Ico_subset]
  exact ⟨x, hxy, Ico_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma slope_lt_derivWithin (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y < derivWithin f S y :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma slope_lt_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
lemma slope_lt_deriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y < deriv f y :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end right
lemma strictMonoOn_derivWithin (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictMonoOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))
lemma strictMonoOn_deriv (hfc : StrictConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))
end StrictConvexOn
section MirrorImage
variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
namespace ConcaveOn
section left
lemma slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y ≤ f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)
lemma slope_le_right_deriv (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y ≤ derivWithin f (Ioi x) x :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt
lemma slope_le_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivWithinAt f f' S x) :
    slope f x y ≤ f' := by
  refine hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy (hfd.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Ioi_iff_exists_Ioc_subset]
  exact ⟨y, hxy, Ioc_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma slope_le_derivWithin (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y ≤ derivWithin f S x :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma slope_le_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt
lemma slope_le_deriv (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : DifferentiableAt ℝ f x) :
    slope f x y ≤ deriv f x :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end left
section right
lemma le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' ≤ slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)
lemma left_deriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
lemma le_slope_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    f' ≤ slope f x y := by
  refine hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy (hf'.mono_of_mem_nhdsWithin ?_)
  rw [mem_nhdsWithin_Iio_iff_exists_Ico_subset]
  exact ⟨x, hxy, Ico_subset_Icc_self.trans (hfc.1.ordConnected.out hx hy)⟩
lemma derivWithin_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma le_slope_of_hasDerivAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
lemma deriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end right
lemma antitoneOn_derivWithin (hfc : ConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    AntitoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))
theorem antitoneOn_deriv (hfc : ConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    AntitoneOn (deriv f) S := by
  simpa only [Pi.neg_def, deriv.neg, neg_neg] using
    (hfc.neg.monotoneOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg
end ConcaveOn
namespace StrictConcaveOn
section left
lemma slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)
lemma slope_lt_right_deriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y < derivWithin f (Ioi x) x :=
  hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)
lemma slope_lt_derivWithin (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y < derivWithin f S x :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma slope_lt_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivAt f f' x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)
lemma slope_lt_deriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    slope f x y < deriv f x :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end left
section right
lemma lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' < slope f x y := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)
lemma left_deriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    f' < slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)
lemma derivWithin_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt
lemma lt_slope_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt
lemma deriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt
end right
lemma strictAntiOn_derivWithin (hfc : StrictConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictAntiOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))
theorem strictAntiOn_deriv (hfc : StrictConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictAntiOn (deriv f) S := by
  simpa only [Pi.neg_def, deriv.neg, neg_neg] using
    (hfc.neg.strictMonoOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg
end StrictConcaveOn
end MirrorImage