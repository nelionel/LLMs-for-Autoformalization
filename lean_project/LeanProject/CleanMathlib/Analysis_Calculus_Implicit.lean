import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.Complemented
noncomputable section
open scoped Topology
open Filter
open ContinuousLinearMap (fst snd smulRight ker_prod)
open ContinuousLinearEquiv (ofBijective)
open LinearMap (ker range)
structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  leftFun : E → F
  leftDeriv : E →L[𝕜] F
  rightFun : E → G
  rightDeriv : E →L[𝕜] G
  pt : E
  left_has_deriv : HasStrictFDerivAt leftFun leftDeriv pt
  right_has_deriv : HasStrictFDerivAt rightFun rightDeriv pt
  left_range : range leftDeriv = ⊤
  right_range : range rightDeriv = ⊤
  isCompl_ker : IsCompl (ker leftDeriv) (ker rightDeriv)
namespace ImplicitFunctionData
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)
@[simp]
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) :=
  rfl
protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.left_range φ.right_range
          φ.isCompl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.left_has_deriv.prod φ.right_has_deriv
def toPartialHomeomorph : PartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toPartialHomeomorph _
def implicitFunction : F → G → E :=
  Function.curry <| φ.toPartialHomeomorph.symm
@[simp]
theorem toPartialHomeomorph_coe : ⇑φ.toPartialHomeomorph = φ.prodFun :=
  rfl
theorem toPartialHomeomorph_apply (x : E) : φ.toPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) :=
  rfl
theorem pt_mem_toPartialHomeomorph_source : φ.pt ∈ φ.toPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toPartialHomeomorph_source
theorem map_pt_mem_toPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) ∈ φ.toPartialHomeomorph.target :=
  φ.toPartialHomeomorph.map_source <| φ.pt_mem_toPartialHomeomorph_source
theorem prod_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h
theorem left_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.fst
theorem right_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.snd
theorem implicitFunction_apply_image :
    ∀ᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse
theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map, φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds]
theorem implicitFunction_hasStrictFDerivAt (g'inv : G →L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse
  simp only [prodFun] at this
  convert this.comp (φ.rightFun φ.pt) ((hasStrictFDerivAt_const _ _).prod (hasStrictFDerivAt_id _))
  simp only [ContinuousLinearMap.ext_iff, (ContinuousLinearMap.comp_apply)] at hg'inv hg'invf ⊢
  simp [ContinuousLinearEquiv.eq_symm_apply, *]
end ImplicitFunctionData
namespace HasStrictFDerivAt
section Complemented
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
section Defs
variable (f f')
@[simp]
def implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : ImplicitFunctionData 𝕜 E F (ker f') where
  leftFun := f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  left_has_deriv := hf
  right_has_deriv :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  left_range := hf'
  right_range := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker)
def implicitToPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : PartialHomeomorph E (F × ker f') :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toPartialHomeomorph
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : F → ker f' → E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction
end Defs
@[simp]
theorem implicitToPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (x : E) :
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x :=
  rfl
theorem implicitToPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : E) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) :=
  rfl
@[simp]
theorem implicitToPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : ker f') :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]
@[simp]
theorem implicitToPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToPartialHomeomorphOfComplemented_apply]
theorem mem_implicitToPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    a ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _
theorem mem_implicitToPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).map_source <|
      hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image
@[simp]
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker)
theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      (ker f').subtypeL 0 := by
  convert (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_hasStrictFDerivAt
    (ker f').subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coe_subtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    simp only [(ContinuousLinearMap.comp_apply), Submodule.coe_subtypeL', Submodule.coe_subtype,
      LinearMap.map_coe_ker, (ContinuousLinearMap.zero_apply)]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]
end Complemented
section FiniteDimensional
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E → F) (f' : E →L[𝕜] F) {a : E}
def implicitToPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    PartialHomeomorph E (F × ker f') :=
  haveI := FiniteDimensional.complete 𝕜 F
  hf.implicitToPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) : F → ker f' → E :=
  Function.curry <| (hf.implicitToPartialHomeomorph f f' hf').symm
variable {f f'}
@[simp]
theorem implicitToPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (x : E) : (hf.implicitToPartialHomeomorph f f' hf' x).fst = f x :=
  rfl
@[simp]
theorem implicitToPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (y : ker f') : hf.implicitToPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_apply_ker ..
@[simp]
theorem implicitToPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitToPartialHomeomorph f f' hf' a = (f a, 0) :=
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_self ..
theorem mem_implicitToPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : a ∈ (hf.implicitToPartialHomeomorph f f' hf').source :=
  haveI := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _
theorem mem_implicitToPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorph f f' hf').target :=
  haveI := FiniteDimensional.complete 𝕜 F
  mem_implicitToPartialHomeomorphOfComplemented_target ..
theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α → F} {g₂ : α → ker f'} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToPartialHomeomorph_source hf')).comp ?_
  rw [implicitToPartialHomeomorph_self]
  exact h₁.prod_mk_nhds h₂
alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  haveI := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..
@[simp]
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  haveI := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToPartialHomeomorph f f' hf' x).snd = x :=
  haveI := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..
theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) (ker f').subtypeL 0 :=
  haveI := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..
end FiniteDimensional
end HasStrictFDerivAt