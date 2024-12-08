import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
open Topology InnerProductSpace Set
noncomputable section
variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x : F}
def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') x L
def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)
def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)
def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)
def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)
@[inherit_doc]
scoped[Gradient] notation "∇" => gradient
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y
open scoped Gradient
variable {s : Set F} {L : Filter F}
theorem hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x :=
  Iff.rfl
theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : F →L[𝕜] 𝕜} {s : Set F} :
    HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, (toDual 𝕜 F).apply_symm_apply frechet]
theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x :=
  Iff.rfl
theorem hasFDerivAt_iff_hasGradientAt {frechet : F →L[𝕜] 𝕜} :
    HasFDerivAt f frechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [hasGradientAt_iff_hasFDerivAt, (toDual 𝕜 F).apply_symm_apply frechet]
alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt
alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt
alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt
alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt
theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient, fderiv_zero_of_not_differentiableAt h, map_zero]
theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)
theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, gradient, (toDual 𝕜 F).apply_symm_apply (fderiv 𝕜 f x)]
  exact h.hasFDerivAt
theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, gradientWithin,
    (toDual 𝕜 F).apply_symm_apply (fderivWithin 𝕜 f s x)]
  exact h.hasFDerivWithinAt
theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.hasFDerivWithinAt.differentiableWithinAt
@[simp]
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ
theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt
theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h
theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient
section OneDimension
variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}
theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (starRingEnd 𝕜 g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (starRingEnd 𝕜 g') = (toDual 𝕜 𝕜) g' := by
    ext; simp
  rwa [HasDerivAtFilter, this]
theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' u L') :
    HasGradientAtFilter g (starRingEnd 𝕜 g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (starRingEnd 𝕜 g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]
theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) :
    HasDerivAt g (starRingEnd 𝕜 g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at h
  simpa using h
theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) :
    HasGradientAt g (starRingEnd 𝕜 g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
  simpa
theorem gradient_eq_deriv : ∇ g u = starRingEnd 𝕜 (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]
end OneDimension
section OneDimensionReal
variable {g : ℝ → ℝ} {g' u : ℝ} {L' : Filter ℝ}
theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' u L' := h.hasDerivAtFilter
theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' u L') :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter
theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt
theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt
theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv
end OneDimensionReal
open Filter
section GradientProperties
theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x :=
  hasFDerivAtFilter_iff_isLittleO ..
theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO
theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO
theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h
theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h
theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h
theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero
end GradientProperties
section congr
variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {t : Set F}
theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  h₀.hasFDerivAtFilter_iff hx (by simp [h₁])
theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]
theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁
theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)
theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)
theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx
theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)
theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]
protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq
end congr
section Const
variable (c : 𝕜) (s x L)
theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter, map_zero]; apply hasFDerivAtFilter_const c x L
theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _
theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x :=
  hasGradientAtFilter_const _ _ _
theorem gradient_const : ∇ (fun _ => c) x = 0 := by
  rw [gradient, fderiv_const, Pi.zero_apply, map_zero]
@[simp]
theorem gradient_const' : (∇ fun _ : 𝕜 => c) = fun _ => 0 :=
  funext fun x => gradient_const x c
end Const
section Continuous
nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL
theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h
theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h
protected theorem HasGradientAt.continuousOn {f' : F → F} (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt
end Continuous