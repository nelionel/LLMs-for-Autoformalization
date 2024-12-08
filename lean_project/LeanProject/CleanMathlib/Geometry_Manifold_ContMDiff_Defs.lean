import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.LocalInvariantProperties
open Set Function Filter ChartedSpace SmoothManifoldWithCorners
open scoped Topology Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {e : PartialHomeomorph M H}
  {e' : PartialHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : ℕ∞}
variable (I I') in
def ContDiffWithinAtProp (n : ℕ∞) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)
theorem contDiffWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]
theorem contDiffWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source
theorem contDiffWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    ContDiffWithinAtProp I 𝓘(𝕜, E') n f s x ↔
      ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl
theorem contDiffWithinAt_localInvariantProp (n : ℕ∞) :
    (contDiffGroupoid ∞ I).LocalInvariantProp (contDiffGroupoid ∞ I')
      (ContDiffWithinAtProp I I' n) where
  is_local {s x u f} u_open xu := by
    have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
    symm
    apply contDiffWithinAt_inter
    have : u ∈ 𝓝 (I.symm (I x)) := by
      rw [ModelWithCorners.left_inv]
      exact u_open.mem_nhds xu
    apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuousAt this
  right_invariance' {s x f e} he hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
    rw [this] at h
    have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I := by simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
    convert (h.comp_inter _ (this.of_le (mod_cast le_top))).mono_of_mem_nhdsWithin _
      using 1
    · ext y; simp only [mfld_simps]
    refine mem_nhdsWithin.mpr
      ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
    mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [h, hy, mfld_simps]
    · simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
      simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
    convert (this.of_le (mod_cast le_top)).comp _ h _
    · ext y; simp only [mfld_simps]
    · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1
theorem contDiffWithinAtProp_mono_of_mem_nhdsWithin
    (n : ℕ∞) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]
@[deprecated (since := "2024-10-31")]
alias contDiffWithinAtProp_mono_of_mem := contDiffWithinAtProp_mono_of_mem_nhdsWithin
theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]
variable (I I') in
def ContMDiffWithinAt (n : ℕ∞) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x
@[deprecated (since := "024-11-21")] alias SmoothWithinAt := ContMDiffWithinAt
variable (I I') in
def ContMDiffAt (n : ℕ∞) (f : M → M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x
theorem contMDiffAt_iff {n : ℕ∞} {f : M → M'} {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
  liftPropAt_iff.trans <| by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl
@[deprecated (since := "024-11-21")] alias SmoothAt := ContMDiffAt
variable (I I') in
def ContMDiffOn (n : ℕ∞) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMDiffWithinAt I I' n f s x
@[deprecated (since := "024-11-21")] alias SmoothOn := ContMDiffOn
variable (I I') in
def ContMDiff (n : ℕ∞) (f : M → M') :=
  ∀ x, ContMDiffAt I I' n f x
@[deprecated (since := "024-11-21")] alias Smooth := ContMDiff
theorem ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m ≤ n) :
    ContMDiffWithinAt I I' m f s x := by
  simp only [ContMDiffWithinAt, LiftPropWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩
theorem ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m ≤ n) : ContMDiffAt I I' m f x :=
  ContMDiffWithinAt.of_le hf le
theorem ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m ≤ n) : ContMDiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le
theorem ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m ≤ n) : ContMDiff I I' m f := fun x =>
  (hf x).of_le le
@[deprecated (since := "2024-11-20")] alias ContMDiff.smooth := ContMDiff.of_le
@[deprecated (since := "2024-11-20")] alias Smooth.contMDiff := ContMDiff.of_le
@[deprecated (since := "2024-11-20")] alias ContMDiffOn.smoothOn := ContMDiffOn.of_le
@[deprecated (since := "2024-11-20")] alias SmoothOn.contMDiffOn := ContMDiffOn.of_le
@[deprecated (since := "2024-11-20")] alias ContMDiffAt.smoothAt := ContMDiffAt.of_le
@[deprecated (since := "2024-11-20")] alias SmoothAt.contMDiffAt := ContMDiffOn.of_le
@[deprecated (since := "2024-11-20")]
alias ContMDiffWithinAt.smoothWithinAt := ContMDiffWithinAt.of_le
@[deprecated (since := "2024-11-20")]
alias SmoothWithinAt.contMDiffWithinAt := ContMDiffWithinAt.of_le
theorem ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : ContMDiffAt I I' n f x :=
  h x
@[deprecated (since := "2024-11-20")] alias Smooth.smoothAt := ContMDiff.contMDiffAt
theorem contMDiffWithinAt_univ : ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x :=
  Iff.rfl
@[deprecated (since := "2024-11-20")] alias smoothWithinAt_univ := contMDiffWithinAt_univ
theorem contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f := by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]
@[deprecated (since := "2024-11-20")] alias smoothOn_univ := contMDiffOn_univ
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl
theorem contMDiffWithinAt_iff' :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
  exact and_congr_right fun hc => contDiffWithinAt_congr_set <|
    hc.extChartAt_symm_preimage_inter_range_eventuallyEq
theorem contMDiffWithinAt_iff_target :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
      and_iff_left_of_imp <| (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWithinAtProp, extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.coe_coe, modelWithCornersSelf_coe,
    chartAt_self_eq, PartialHomeomorph.refl_apply, id_comp]
  rfl
@[deprecated (since := "2024-11-20")] alias smoothWithinAt_iff := contMDiffWithinAt_iff
@[deprecated (since := "2024-11-20")]
alias smoothWithinAt_iff_target := contMDiffWithinAt_iff_target
theorem contMDiffAt_iff_target {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x := by
  rw [ContMDiffAt, ContMDiffAt, contMDiffWithinAt_iff_target, continuousWithinAt_univ]
@[deprecated (since := "2024-11-20")] alias smoothAt_iff_target := contMDiffAt_iff_target
section SmoothManifoldWithCorners
theorem contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    [SmoothManifoldWithCorners I M] (he : e ∈ maximalAtlas I M) (hx : x ∈ e.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s ∩ range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtProp_self_source,
    ContDiffWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl
theorem contMDiffWithinAt_iff_source_of_mem_source
    [SmoothManifoldWithCorners I M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'
theorem contMDiffAt_iff_source_of_mem_source
    [SmoothManifoldWithCorners I M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffAt I I' n f x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x') := by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]
theorem contMDiffWithinAt_iff_target_of_mem_source
    [SmoothManifoldWithCorners I' M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x := by
  simp_rw [ContMDiffWithinAt]
  rw [(contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy,
    and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source (I := I')] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl
theorem contMDiffAt_iff_target_of_mem_source
    [SmoothManifoldWithCorners I' M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) x := by
  rw [ContMDiffAt, contMDiffWithinAt_iff_target_of_mem_source hy, continuousWithinAt_univ,
    ContMDiffAt]
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart he hx he' hy
theorem contMDiffWithinAt_iff_image {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_set ?_
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs hx]
theorem contMDiffWithinAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy
theorem contMDiffWithinAt_iff_of_mem_source' {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_set ?_
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← e.image_source_inter_eq',
    ← map_extChartAt_nhdsWithin_eq_image' hx,
    ← map_extChartAt_nhdsWithin' hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)
theorem contMDiffAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (contMDiffWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]
theorem contMDiffOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)
theorem contMDiffOn_iff_of_mem_maximalAtlas' (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  (contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans <| and_iff_right_of_imp fun h ↦
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn
theorem contMDiffOn_iff_of_subset_source {x : M} {y : M'} (hs : s ⊆ (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hs
    h2s
theorem contMDiffOn_iff_of_subset_source' {x : M} {y : M'} (hs : s ⊆ (extChartAt I x).source)
    (h2s : MapsTo f s (extChartAt I' y).source) :
    ContMDiffOn I I' n f s ↔
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s
theorem contMDiffOn_iff :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w ∈ s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w ∈ (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w ∈ (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert ((contMDiffWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [ContDiffWithinAtProp]
    convert hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac
theorem contMDiffOn_iff_target :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ y : M',
          ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) := by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    PartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0
@[deprecated (since := "2024-11-20")] alias smoothOn_iff := contMDiffOn_iff
@[deprecated (since := "2024-11-20")] alias smoothOn_iff_target := contMDiffOn_iff_target
theorem contMDiff_iff :
    ContMDiff I I' n f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) := by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuous_iff_continuousOn_univ]
theorem contMDiff_iff_target :
    ContMDiff I I' n f ↔
      Continuous f ∧ ∀ y : M',
        ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) := by
  rw [← contMDiffOn_univ, contMDiffOn_iff_target]
  simp [continuous_iff_continuousOn_univ]
@[deprecated (since := "2024-11-20")] alias smooth_iff := contMDiff_iff
@[deprecated (since := "2024-11-20")] alias smooth_iff_target := contMDiff_iff_target
end SmoothManifoldWithCorners
theorem ContMDiffWithinAt.of_succ {n : ℕ} (h : ContMDiffWithinAt I I' n.succ f s x) :
    ContMDiffWithinAt I I' n f s x :=
  h.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n))
theorem ContMDiffAt.of_succ {n : ℕ} (h : ContMDiffAt I I' n.succ f x) : ContMDiffAt I I' n f x :=
  ContMDiffWithinAt.of_succ h
theorem ContMDiffOn.of_succ {n : ℕ} (h : ContMDiffOn I I' n.succ f s) : ContMDiffOn I I' n f s :=
  fun x hx => (h x hx).of_succ
theorem ContMDiff.of_succ {n : ℕ} (h : ContMDiff I I' n.succ f) : ContMDiff I I' n f := fun x =>
  (h x).of_succ
theorem ContMDiffWithinAt.continuousWithinAt (hf : ContMDiffWithinAt I I' n f s x) :
    ContinuousWithinAt f s x :=
  hf.1
theorem ContMDiffAt.continuousAt (hf : ContMDiffAt I I' n f x) : ContinuousAt f x :=
  (continuousWithinAt_univ _ _).1 <| ContMDiffWithinAt.continuousWithinAt hf
theorem ContMDiffOn.continuousOn (hf : ContMDiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).continuousWithinAt
theorem ContMDiff.continuous (hf : ContMDiff I I' n f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
theorem contMDiffWithinAt_top :
    ContMDiffWithinAt I I' ⊤ f s x ↔ ∀ n : ℕ, ContMDiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, contDiffWithinAt_infty.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_infty.2 fun n => (H n).2⟩⟩
theorem contMDiffAt_top : ContMDiffAt I I' ⊤ f x ↔ ∀ n : ℕ, ContMDiffAt I I' n f x :=
  contMDiffWithinAt_top
theorem contMDiffOn_top : ContMDiffOn I I' ⊤ f s ↔ ∀ n : ℕ, ContMDiffOn I I' n f s :=
  ⟨fun h _ => h.of_le le_top, fun h x hx => contMDiffWithinAt_top.2 fun n => h n x hx⟩
theorem contMDiff_top : ContMDiff I I' ⊤ f ↔ ∀ n : ℕ, ContMDiff I I' n f :=
  ⟨fun h _ => h.of_le le_top, fun h x => contMDiffWithinAt_top.2 fun n => h n x⟩
theorem contMDiffWithinAt_iff_nat :
    ContMDiffWithinAt I I' n f s x ↔ ∀ m : ℕ, (m : ℕ∞) ≤ n → ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm => h.of_le hm, fun h => ?_⟩
  cases' n with n
  · exact contMDiffWithinAt_top.2 fun n => h n le_top
  · exact h n le_rfl
theorem ContMDiffWithinAt.mono_of_mem_nhdsWithin
    (hf : ContMDiffWithinAt I I' n f s x) (hts : s ∈ 𝓝[t] x) :
    ContMDiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin
    (contDiffWithinAtProp_mono_of_mem_nhdsWithin n) hf hts
@[deprecated (since := "2024-10-31")]
alias ContMDiffWithinAt.mono_of_mem := ContMDiffWithinAt.mono_of_mem_nhdsWithin
theorem ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t ⊆ s) :
    ContMDiffWithinAt I I' n f t x :=
  hf.mono_of_mem_nhdsWithin <| mem_of_superset self_mem_nhdsWithin hts
theorem contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_set h
theorem ContMDiffWithinAt.congr_set (h : ContMDiffWithinAt I I' n f s x) (hst : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f t x :=
  (contMDiffWithinAt_congr_set hst).1 h
@[deprecated (since := "2024-10-23")]
alias contMDiffWithinAt_congr_nhds := contMDiffWithinAt_congr_set
theorem contMDiffWithinAt_insert_self :
    ContMDiffWithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
  refine Iff.rfl.and <| (contDiffWithinAt_congr_set ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin, nhdsWithin_insert, Filter.map_sup, Filter.map_pure,
    ← nhdsWithin_eq_iff_eventuallyEq]
alias ⟨ContMDiffWithinAt.of_insert, _⟩ := contMDiffWithinAt_insert_self
protected theorem ContMDiffWithinAt.insert (h : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I' n f (insert x s) x :=
  contMDiffWithinAt_insert_self.2 h
theorem contMDiffWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x := by
  have : T1Space M := I.t1Space M
  rw [← contMDiffWithinAt_insert_self (s := s), ← contMDiffWithinAt_insert_self (s := t)]
  exact contMDiffWithinAt_congr_set (eventuallyEq_insert h)
protected theorem ContMDiffAt.contMDiffWithinAt (hf : ContMDiffAt I I' n f x) :
    ContMDiffWithinAt I I' n f s x :=
  ContMDiffWithinAt.mono hf (subset_univ _)
@[deprecated (since := "2024-11-20")] alias SmoothAt.smoothWithinAt := ContMDiffAt.contMDiffWithinAt
theorem ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t ⊆ s) : ContMDiffOn I I' n f t :=
  fun x hx => (hf x (hts hx)).mono hts
protected theorem ContMDiff.contMDiffOn (hf : ContMDiff I I' n f) : ContMDiffOn I I' n f s :=
  fun x _ => (hf x).contMDiffWithinAt
@[deprecated (since := "2024-11-20")] alias Smooth.smoothOn := ContMDiff.contMDiffOn
theorem contMDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter' ht
theorem contMDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter ht
protected theorem ContMDiffWithinAt.contMDiffAt
    (h : ContMDiffWithinAt I I' n f s x) (ht : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_of_liftPropWithinAt h ht
@[deprecated (since := "2024-11-20")] alias SmoothWithinAt.smoothAt := ContMDiffWithinAt.contMDiffAt
protected theorem ContMDiffOn.contMDiffAt (h : ContMDiffOn I I' n f s) (hx : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (h x (mem_of_mem_nhds hx)).contMDiffAt hx
@[deprecated (since := "2024-11-20")] alias SmoothOn.smoothAt := ContMDiffOn.contMDiffAt
theorem contMDiffOn_iff_source_of_mem_maximalAtlas [SmoothManifoldWithCorners I M]
    (he : e ∈ maximalAtlas I M) (hs : s ⊆ e.source) :
    ContMDiffOn I I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_set
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs (hs hx)]
theorem contMDiffWithinAt_iff_contMDiffOn_nhds
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] {n : ℕ} :
    ContMDiffWithinAt I I' n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContMDiffOn I I' n f u := by
  wlog hxs : x ∈ s generalizing s
  · rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  refine ⟨fun h ↦ ?_, fun ⟨u, hmem, hu⟩ ↦
    (hu _ (mem_of_mem_nhdsWithin hxs hmem)).mono_of_mem_nhdsWithin hmem⟩
  rcases (contMDiffWithinAt_iff'.1 h).2.contDiffOn le_rfl (by simp) with ⟨v, hmem, hsub, hv⟩
  have hxs' : extChartAt I x x ∈ (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source) :=
    ⟨(extChartAt I x).map_source (mem_extChartAt_source _), by rwa [extChartAt_to_inv], by
      rw [extChartAt_to_inv]; apply mem_extChartAt_source⟩
  rw [insert_eq_of_mem hxs'] at hmem hsub
  refine ⟨(extChartAt I x).symm '' v, ?_, ?_⟩
  · rw [← map_extChartAt_symm_nhdsWithin (I := I),
      h.1.nhdsWithin_extChartAt_symm_preimage_inter_range (I := I) (I' := I')]
    exact image_mem_map hmem
  · have hv₁ : (extChartAt I x).symm '' v ⊆ (extChartAt I x).source :=
      image_subset_iff.2 fun y hy ↦ (extChartAt I x).map_target (hsub hy).1
    have hv₂ : MapsTo f ((extChartAt I x).symm '' v) (extChartAt I' (f x)).source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hsub hy).2.2
    rwa [contMDiffOn_iff_of_subset_source' hv₁ hv₂, PartialEquiv.image_symm_image_of_subset_target]
    exact hsub.trans inter_subset_left
theorem ContMDiffWithinAt.contMDiffOn'
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
    {m : ℕ} (hm : (m : ℕ∞) ≤ n)
    (h : ContMDiffWithinAt I I' n f s x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' m f (insert x s ∩ u) := by
  rcases contMDiffWithinAt_iff_contMDiffOn_nhds.1 (h.of_le hm) with ⟨t, ht, h't⟩
  rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
  rw [inter_comm] at hu
  exact ⟨u, u_open, xu, h't.mono hu⟩
theorem ContMDiffWithinAt.contMDiffOn
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
    {m : ℕ} (hm : (m : ℕ∞) ≤ n)
    (h : ContMDiffWithinAt I I' n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContMDiffOn I I' m f u := by
  let ⟨_u, uo, xu, h⟩ := h.contMDiffOn' hm
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩
theorem contMDiffAt_iff_contMDiffOn_nhds
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] {n : ℕ} :
    ContMDiffAt I I' n f x ↔ ∃ u ∈ 𝓝 x, ContMDiffOn I I' n f u := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds, nhdsWithin_univ]
theorem contMDiffAt_iff_contMDiffAt_nhds
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] {n : ℕ} :
    ContMDiffAt I I' n f x ↔ ∀ᶠ x' in 𝓝 x, ContMDiffAt I I' n f x' := by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds_iff.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'
theorem contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] {n : ℕ} :
    ContMDiffWithinAt I I' n f s x ↔
      ∀ᶠ x' in 𝓝[insert x s] x, ContMDiffWithinAt I I' n f s x' := by
  refine ⟨?_, fun h ↦ mem_of_mem_nhdsWithin (mem_insert x s) h⟩
  rw [contMDiffWithinAt_iff_contMDiffOn_nhds]
  rintro ⟨u, hu, h⟩
  filter_upwards [hu, eventually_mem_nhdsWithin_iff.mpr hu] with x' h'x' hx'
  apply (h x' h'x').mono_of_mem_nhdsWithin
  exact nhdsWithin_mono _ (subset_insert x s) hx'
theorem ContMDiffWithinAt.congr (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr h h₁ hx
theorem contMDiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff h₁ hx
theorem ContMDiffWithinAt.congr_of_mem
    (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_mem h h₁ hx
theorem contMDiffWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_mem h₁ hx
theorem ContMDiffWithinAt.congr_of_eventuallyEq (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx
theorem ContMDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq_of_mem h h₁ hx
theorem Filter.EventuallyEq.contMDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx
theorem ContMDiffAt.congr_of_eventuallyEq (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_of_eventuallyEq h h₁
theorem Filter.EventuallyEq.contMDiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x ↔ ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_iff_of_eventuallyEq h₁
theorem ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr h h₁
theorem contMDiffOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr_iff h₁
theorem ContMDiffOn.congr_mono (hf : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s₁, f₁ y = f y)
    (hs : s₁ ⊆ s) : ContMDiffOn I I' n f₁ s₁ :=
  (hf.mono hs).congr h₁
theorem contMDiffOn_of_locally_contMDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f (s ∩ u)) : ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_locally_liftPropOn h
theorem contMDiff_of_locally_contMDiffOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f u) :
    ContMDiff I I' n f :=
  (contDiffWithinAt_localInvariantProp n).liftProp_of_locally_liftPropOn h