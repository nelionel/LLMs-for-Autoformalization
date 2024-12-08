import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.LocalInvariantProperties
noncomputable section
open scoped Topology ContDiff
open Set ChartedSpace
section DerivativesDefinitions
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']
variable (I I') in
def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Set.range I) (I x)
open scoped Manifold
theorem differentiableWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) I' f s x ↔ DifferentiableWithinAt 𝕜 (I' ∘ f) s x := by
  simp_rw [DifferentiableWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]
theorem DifferentiableWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAtProp_self_source
theorem differentiableWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    DifferentiableWithinAtProp I 𝓘(𝕜, E') f s x ↔
      DifferentiableWithinAt 𝕜 (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl
theorem differentiableWithinAt_localInvariantProp :
    (contDiffGroupoid ∞ I).LocalInvariantProp (contDiffGroupoid ∞ I')
      (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ Set.range I = I.symm ⁻¹' s ∩ Set.range I ∩ I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp, DifferentiableWithinAtProp, this]
      symm
      apply differentiableWithinAt_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
      convert (h.comp' _ (this.differentiableWithinAt (mod_cast le_top))).mono_of_mem_nhdsWithin _
        using 1
      · ext y; simp only [mfld_simps]
      refine
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert (this.differentiableWithinAt (mod_cast le_top)).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }
@[deprecated (since := "2024-10-10")]
alias differentiable_within_at_localInvariantProp := differentiableWithinAt_localInvariantProp
variable (I) in
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
variable (I) in
def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x
variable (I I') in
def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x
theorem mdifferentiableWithinAt_iff' (f : M → M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) := by
  rw [MDifferentiableWithinAt, liftPropWithinAt_iff']; rfl
@[deprecated (since := "2024-04-30")]
alias mdifferentiableWithinAt_iff_liftPropWithinAt := mdifferentiableWithinAt_iff'
theorem MDifferentiableWithinAt.continuousWithinAt {f : M → M'} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.1
theorem MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
    {f : M → M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.2
variable (I I') in
def MDifferentiableAt (f : M → M') (x : M) :=
  LiftPropAt (DifferentiableWithinAtProp I I') f x
theorem mdifferentiableAt_iff (f : M → M') (x : M) :
    MDifferentiableAt I I' f x ↔ ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) := by
  rw [MDifferentiableAt, liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter]
  rfl
@[deprecated (since := "2024-04-30")]
alias mdifferentiableAt_iff_liftPropAt := mdifferentiableAt_iff
theorem MDifferentiableAt.continuousAt {f : M → M'} {x : M} (hf : MDifferentiableAt I I' f x) :
    ContinuousAt f x :=
  mdifferentiableAt_iff .. |>.1 hf |>.1
theorem MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt {f : M → M'} {x : M}
    (hf : MDifferentiableAt I I' f x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) :=
  mdifferentiableAt_iff .. |>.1 hf |>.2
variable (I I') in
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x
variable (I I') in
def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x
variable (I I') in
def PartialHomeomorph.MDifferentiable (f : PartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target
variable (I I') in
def HasMFDerivWithinAt (f : M → M') (s : Set M) (x : M)
    (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
variable (I I') in
def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
open Classical in
variable (I I') in
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0
open Classical in
variable (I I') in
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0
variable (I I') in
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
variable (I I') in
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
end DerivativesDefinitions