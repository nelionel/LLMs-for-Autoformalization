import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
open Function Set Filter Metric
open scoped Topology NNReal
noncomputable section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
open Asymptotics Filter Metric Set
open ContinuousLinearMap (id)
namespace HasStrictFDerivAt
theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) {c : ℝ≥0} (hc : Subsingleton E ∨ 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  cases' hc with hE hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩
theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) (h : LinearMap.range f' = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, half_pos, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (NNReal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]
variable {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
theorem approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ s : Set E, a ∈ s ∧ IsOpen s ∧
      ApproximatesLinearOn f (f' : E →L[𝕜] F) s (‖(f'.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
    hf.approximates_deriv_on_nhds <|
      f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos <| inv_pos.2 hf'
variable (f)
variable [CompleteSpace E]
def toPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : PartialHomeomorph E F :=
  ApproximatesLinearOn.toPartialHomeomorph f (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
      NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.1
variable {f}
@[simp]
theorem toPartialHomeomorph_coe (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    (hf.toPartialHomeomorph f : E → F) = f :=
  rfl
theorem mem_toPartialHomeomorph_source (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    a ∈ (hf.toPartialHomeomorph f).source :=
  (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1
theorem image_mem_toPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    f a ∈ (hf.toPartialHomeomorph f).target :=
  (hf.toPartialHomeomorph f).map_source hf.mem_toPartialHomeomorph_source
theorem map_nhds_eq_of_equiv (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toPartialHomeomorph f).map_nhds_eq hf.mem_toPartialHomeomorph_source
variable (f f' a)
def localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.toPartialHomeomorph f).symm
variable {f f' a}
theorem localInverse_def (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toPartialHomeomorph f).symm :=
  rfl
theorem eventually_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toPartialHomeomorph f).eventually_left_inverse hf.mem_toPartialHomeomorph_source
@[simp]
theorem localInverse_apply_image (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds
theorem eventually_right_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toPartialHomeomorph f).eventually_right_inverse' hf.mem_toPartialHomeomorph_source
theorem localInverse_continuousAt (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toPartialHomeomorph f).continuousAt_symm hf.image_mem_toPartialHomeomorph_target
theorem localInverse_tendsto (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toPartialHomeomorph f).tendsto_symm hf.mem_toPartialHomeomorph_source
theorem localInverse_unique (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : ∀ᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
  eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse <|
    (hf.toPartialHomeomorph f).tendsto_symm hf.mem_toPartialHomeomorph_source
theorem to_localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.toPartialHomeomorph f).hasStrictFDerivAt_symm hf.image_mem_toPartialHomeomorph_target <| by
    simpa [← localInverse_def] using hf
theorem to_local_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.to_localInverse.congr_of_eventuallyEq <| (hf.localInverse_unique hg).mono fun _ => Eq.symm
end HasStrictFDerivAt
theorem isOpenMap_of_hasStrictFDerivAt_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
    (hf : ∀ x, HasStrictFDerivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge
@[deprecated (since := "2024-03-23")]
alias open_map_of_strict_fderiv_equiv := isOpenMap_of_hasStrictFDerivAt_equiv