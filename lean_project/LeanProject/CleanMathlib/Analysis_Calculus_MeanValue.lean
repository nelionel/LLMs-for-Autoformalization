import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.RCLike.Basic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]
open Metric Set Asymptotics ContinuousLinearMap Filter
open scoped Topology NNReal
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prod hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  cases' hxB.lt_or_eq with hxB hxB
  · 
    refine nonempty_of_mem (inter_mem ?_ (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hy⟩))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsWithin_Ioi xab) this
    exact this.mono fun y => le_of_lt
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y :=
      (hf'.and_eventually (HB.and (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hy⟩))).exists
    refine ⟨z, ?_, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
    · intro x _ _
      rw [mul_one]
      exact (lt_add_iff_pos_right _).2 hr
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 :=
    continuousWithinAt_const.add (continuousWithinAt_id.mul continuousWithinAt_const)
  convert continuousWithinAt_const.closure_le _ this (Hr x hx) using 1 <;> simp
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)
section
variable {f : ℝ → E} {a b : ℝ}
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub continuousOn_const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simpa using (hf' x hx).sub (hasDerivWithinAt_const _ _ _)
  let B x := C * (x - a)
  have hB : ∀ x, HasDerivAt B C x := by
    intro x
    simpa using (hasDerivAt_const x C).mul ((hasDerivAt_id x).sub (hasDerivAt_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only [g, B]; rw [sub_self, norm_zero, sub_self, mul_zero]
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Ici hx)
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
    (bound : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖f' x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖derivWithin f (Icc (0 : ℝ) 1) x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)
theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) : ∀ x ∈ Icc a b, f x = f a := by
  have : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this
theorem constant_of_derivWithin_zero (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, derivWithin f (Icc a b) x = 0) : ∀ x ∈ Icc a b, f x = f a := by
  have H : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx
variable {f' g : ℝ → E}
theorem eq_of_has_deriv_right_eq (derivf : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀ y ∈ Icc a b, f y = g y := by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using (derivf y hy).sub (derivg y hy)
theorem eq_of_derivWithin_eq (fdiff : DifferentiableOn ℝ f (Icc a b))
    (gdiff : DifferentiableOn ℝ g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    ∀ y ∈ Icc a b, f y = g y := by
  have A : ∀ y ∈ Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsWithin_Ici hy)
  have B : ∀ y ∈ Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsWithin_Ici hy)
  exact
    eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
      gdiff.continuousOn hi
end
section
namespace Convex
variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f g : E → G} {C : ℝ} {s : Set E} {x y : E} {f' g' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}
instance (priority := 100) : PathConnectedSpace 𝕜 := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  infer_instance
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  set g := (AffineMap.lineMap x y : ℝ → E)
  have segm : MapsTo g (Icc 0 1 : Set ℝ) s := hs.mapsTo_lineMap xs ys
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (g t) (y - x)‖ ≤ C * ‖y - x‖ := fun t ht =>
    le_of_opNorm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : ℝ≥0}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C)
    (hs : Convex ℝ s) : LipschitzOnWith C f s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Convex ℝ s)
    {f : E → G} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (K : ℝ≥0) (hK : ‖f' x‖₊ < K) :
    ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : ∃ ε > 0,
      ball x ε ∩ s ⊆ { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s ∩ ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ ε0), ?_⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hε hy).1.mono inter_subset_left) fun y hy => (hε hy).2.le
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <|
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont
theorem norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le {C : ℝ≥0} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys
theorem lipschitzOnWith_of_nnnorm_fderiv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound
theorem _root_.lipschitzWith_of_nnnorm_fderiv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖fderiv 𝕜 f x‖₊ ≤ C) : LipschitzWith C f := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hf x) (fun x _ ↦ bound x) convex_univ
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ := by
  let g y := f y - φ y
  have hg : ∀ x ∈ s, HasFDerivWithinAt g (f' x - φ) s x := fun x xs =>
    (hf x xs).sub φ.hasFDerivWithinAt
  calc
    ‖f y - f x - φ (y - x)‖ = ‖f y - f x - (φ y - φ x)‖ := by simp
    _ = ‖f y - φ y - (f x - φ x)‖ := by congr 1; abel
    _ = ‖g y - g x‖ := by simp
    _ ≤ C * ‖y - x‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg bound hs xs ys
theorem norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys
theorem is_const_of_fderivWithin_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy
theorem _root_.is_const_of_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0)
    (x y : E) : f x = f y := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial
theorem eqOn_of_fderivWithin_eq (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = fderivWithin 𝕜 g s x) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz), sub_eq_zero, hf' _ hz]
theorem _root_.eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E → G}
    (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
    (hf' : ∀ x, fderiv 𝕜 f x = fderiv 𝕜 g x) (x : E) (hfgx : f x = g x) : f = g := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  suffices Set.univ.EqOn f g from funext fun x => this <| mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa using hf' _) (mem_univ _) hfgx
end Convex
namespace Convex
variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}
theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs
theorem norm_image_sub_le_of_norm_derivWithin_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖derivWithin f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys
theorem lipschitzOnWith_of_nnnorm_derivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : DifferentiableOn 𝕜 f s) (bound : ∀ x ∈ s, ‖derivWithin f s x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys
theorem lipschitzOnWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound
theorem _root_.lipschitzWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖deriv f x‖₊ ≤ C) : LipschitzWith C f :=
  lipschitzOnWith_univ.1 <|
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0)
    (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf (fun z => by ext; simp [← deriv_fderiv, hf']) _ _
end Convex
end
section Interval
variable (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hfd : DifferentiableOn ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn ℝ g (Ioo a b))
include hab hfc hff' hgc hgg' in
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
include hab in
theorem exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert this using 2
    ring
  have hhb : Tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert this using 2
    ring
  let h' x := (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_hasDerivAt_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
include hab hfc hff' in
theorem exists_hasDerivAt_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc
include hab hfc hgc hgd hfd in
theorem exists_ratio_deriv_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt
include hab in
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hdf : DifferentiableOn ℝ f <| Ioo a b) (hdg : DifferentiableOn ℝ g <| Ioo a b)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb
include hab hfc hfd in
theorem exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt
include hab hfc hfd in
theorem exists_deriv_eq_slope' : ∃ c ∈ Ioo a b, deriv f c = slope f a b := by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : ContinuousWithinAt f (Ici a) a
  case neg =>
    intro hcontra
    have := hcontra.continuousWithinAt
    rw [← ContinuousWithinAt.diff_iff this] at hcont_at_a
    simp at hcont_at_a
  case pos =>
    intro hdiff
    replace hdiff := hdiff.hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.diff_singleton_eq_self not_mem_Ioi_self] at hdiff
    have h₀ : ∀ᶠ b in 𝓝[>] a,
        ∀ x ∈ Ioc a b, max (derivWithin f (Ioi a) a + 1) 0 < derivWithin f (Ioi a) x := by
      rw [(nhdsWithin_Ioi_basis a).eventually_iff]
      rw [(nhdsWithin_Ioi_basis a).tendsto_left_iff] at hf
      obtain ⟨b, hab, hb⟩ := hf (Ioi (max (derivWithin f (Ioi a) a + 1) 0)) (Ioi_mem_atTop _)
      refine ⟨b, hab, fun x hx z hz => ?_⟩
      simp only [MapsTo, mem_Ioo, mem_Ioi, and_imp] at hb
      exact hb hz.1 <| hz.2.trans_lt hx.2
    have h₁ : ∀ᶠ b in 𝓝[>] a, slope f a b < derivWithin f (Ioi a) a + 1 := by
      rw [(nhds_basis_Ioo _).tendsto_right_iff] at hdiff
      specialize hdiff ⟨derivWithin f (Ioi a) a - 1, derivWithin f (Ioi a) a + 1⟩ <| by simp
      filter_upwards [hdiff] with z hz using hz.2
    have hcontra : ∀ᶠ _ in 𝓝[>] a, False := by
      filter_upwards [h₀, h₁, eventually_mem_nhdsWithin] with b hb hslope (hab : a < b)
      have hdiff' : DifferentiableOn ℝ f (Ioc a b) := fun z hz => by
        refine DifferentiableWithinAt.mono (t := Ioi a) ?_ Ioc_subset_Ioi_self
        have : derivWithin f (Ioi a) z ≠ 0 := ne_of_gt <| by
          simp_all only [mem_Ioo, and_imp, mem_Ioc, max_lt_iff]
        exact differentiableWithinAt_of_derivWithin_ne_zero this
      have hcont_Ioc : ∀ z ∈ Ioc a b, ContinuousWithinAt f (Icc a b) z := by
        intro z hz''
        refine (hdiff'.continuousOn z hz'').mono_of_mem_nhdsWithin ?_
        have hfinal : 𝓝[Ioc a b] z = 𝓝[Icc a b] z := by
          refine nhdsWithin_eq_nhdsWithin' (s := Ioi a) (Ioi_mem_nhds hz''.1) ?_
          simp only [Ioc_inter_Ioi, le_refl, sup_of_le_left]
          ext y
          exact ⟨fun h => ⟨mem_Icc_of_Ioc h, mem_of_mem_inter_left h⟩, fun ⟨H1, H2⟩ => ⟨H2, H1.2⟩⟩
        rw [← hfinal]
        exact self_mem_nhdsWithin
      have hcont : ContinuousOn f (Icc a b) := by
        intro z hz
        by_cases hz' : z = a
        · rw [hz']
          exact hcont_at_a.mono Icc_subset_Ici_self
        · exact hcont_Ioc z ⟨lt_of_le_of_ne hz.1 (Ne.symm hz'), hz.2⟩
      obtain ⟨x, hx₁, hx₂⟩ :=
        exists_deriv_eq_slope' f hab hcont (hdiff'.mono (Ioo_subset_Ioc_self))
      specialize hb x ⟨hx₁.1, le_of_lt hx₁.2⟩
      replace hx₂ : derivWithin f (Ioi a) x = slope f a b := by
        have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx₁.1]
        rwa [derivWithin_of_mem_nhds this]
      rw [hx₂, max_lt_iff] at hb
      linarith
    simp [Filter.eventually_false_iff_eq_bot, ← not_mem_closure_iff_nhdsWithin_eq_bot] at hcontra
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [Pi.neg_def, deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsWithin_Iio_basis a).eventually_iff] at hf
    rw [EventuallyEq, (nhdsWithin_Ioi_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, hb₂⟩ := hf
    refine ⟨-b, by linarith, fun x hx => ?_⟩
    simp only [Pi.neg_apply, Function.comp_apply]
    suffices deriv f' x = deriv f (-x) * deriv (Neg.neg : ℝ → ℝ) x by simpa using this
    refine deriv_comp x (differentiableAt_of_deriv_ne_zero ?_) (by fun_prop)
    rw [mem_Ioo] at hx
    have h₁ : -x ∈ Ioo b a := ⟨by linarith, by linarith⟩
    have h₂ : deriv f (-x) ≤ -1 := hb₂ h₁
    exact ne_of_lt (by linarith)
  have hmain : ¬ DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi f' <| Tendsto.congr' hderiv.symm ?_
    refine Tendsto.comp (g := -deriv f) ?_ tendsto_neg_nhdsWithin_Ioi_neg
    exact Tendsto.comp (g := Neg.neg) tendsto_neg_atBot_atTop hf
  intro h
  have : DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine DifferentiableWithinAt.comp (g := f) (f := Neg.neg) (t := Iio a) (-a) ?_ ?_ ?_
    · simp [h]
    · fun_prop
    · intro x
      simp [neg_lt]
  exact hmain this
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [Pi.neg_def, deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg
end Interval
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x < y → C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := ha ▸ hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff₀ (sub_pos.2 hxy)).1 this
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x ≤ y → C * (y - x) ≤ f y - f x := by
  intro x hx y hy hxy
  cases' eq_or_lt_of_le hxy with hxy' hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C ≤ (f y - f x) / (y - x) := ha ▸ hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff₀ (sub_pos.2 hxy')).1 this
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (lt_hf' : ∀ x ∈ interior D, deriv f x < C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x < y) : f y - f x < C * (y - x) :=
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.neg, neg_lt_neg_iff]
    exact lt_hf' x hx
  by linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x hx y hy hxy]
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.neg, neg_le_neg_iff]
    exact le_hf' x hx
  by linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x hx y hy hxy]
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy
theorem strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D := by
  intro x hx y hy
  have : DifferentiableOn ℝ f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy
theorem strictMono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMonoOn_univ.1 <| strictMonoOn_of_deriv_pos convex_univ (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x
lemma strictMonoOn_of_hasDerivWithinAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx
@[deprecated (since := "2024-03-02")]
alias StrictMonoOn_of_hasDerivWithinAt_pos := strictMonoOn_of_hasDerivWithinAt_pos
lemma strictMono_of_hasDerivAt_pos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < f' x) : StrictMono f :=
  strictMono_of_deriv_pos fun x ↦ by rw [(hf _).deriv]; exact hf' _
theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) : MonotoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
    Monotone f :=
  monotoneOn_univ.1 <|
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x
lemma monotoneOn_of_hasDerivWithinAt_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx
lemma monotone_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : 0 ≤ f') : Monotone f :=
  monotone_of_deriv_nonneg (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _
theorem strictAntiOn_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y
theorem strictAnti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strictAntiOn_univ.1 <| strictAntiOn_of_deriv_neg convex_univ
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x
lemma strictAntiOn_of_hasDerivWithinAt_neg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x < 0) : StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx
@[deprecated (since := "2024-03-02")]
alias StrictAntiOn_of_hasDerivWithinAt_pos := strictAntiOn_of_hasDerivWithinAt_neg
lemma strictAnti_of_hasDerivAt_neg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, f' x < 0) : StrictAnti f :=
  strictAnti_of_deriv_neg fun x ↦ by rw [(hf _).deriv]; exact hf' _
@[deprecated (since := "2024-03-02")]
alias strictAnti_of_hasDerivAt_pos := strictAnti_of_hasDerivAt_neg
theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
    Antitone f :=
  antitoneOn_univ.1 <|
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x
lemma antitoneOn_of_hasDerivWithinAt_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x ≤ 0) : AntitoneOn f D :=
  antitoneOn_of_deriv_nonpos hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx
lemma antitone_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : f' ≤ 0) : Antitone f :=
  antitone_of_deriv_nonpos (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _
theorem domain_mvt {f : E → ℝ} {s : Set E} {x y : E} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∃ z ∈ segment ℝ x y, f y - f x = f' z (y - x) := by
  set g : ℝ → E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : ℝ) 1
  have hsub : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  have hfg : ∀ t ∈ I, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) I t := fun t ht =>
    (hf _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  have hMVT : ∃ t ∈ Ioo (0 : ℝ) 1, f' (g t) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine exists_hasDerivAt_eq_slope (f ∘ g) _ (by norm_num) ?_ ?_
    · exact fun t Ht => (hfg t Ht).continuousWithinAt
    · exact fun t Ht => (hfg t <| hsub Ht).hasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  rw [segment_eq_image_lineMap, exists_mem_image]
  refine ⟨t, hsub Ht, ?_⟩
  simpa [g] using hMVT'.symm
section RCLike
variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (hder : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictFDerivAt f (f' x) x := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  rcases Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine ⟨ε, ε0, ?_⟩
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prod_mk_mem_set_prod_eq] at h
  have hf' : ∀ x' ∈ ball x ε, ‖f' x' - f' x‖ ≤ c := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  refine (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le' ?_ hf' h.2 h.1
  exact fun y hy => (hε hy).1.hasFDerivWithinAt
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 → G} {x : 𝕜}
    (hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictDerivAt f (f' x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt) <|
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont
end RCLike