import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.LocallyConstant.Basic
open scoped Manifold Topology Filter
open Function Set Filter Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
theorem Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M → F} {c : M}
    (hd : ∀ᶠ z in 𝓝 c, MDifferentiableAt I 𝓘(ℂ, F) f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c, H₁]
  rw [← H₂, eventually_map]
  replace hd : ∀ᶠ y in 𝓝 (e c), DifferentiableAt ℂ (f ∘ e.symm) y := by
    have : e.target ∈ 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y ∈ (chartAt H c).source := by
      rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) ∈ (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy, hI, differentiableWithinAt_univ,
      e.right_inv hyt] at hy₂
    exact hy₂.2
  convert norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _).symm
  · simpa only [e, IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using hc
namespace MDifferentiableOn
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : M → F} {U : Set M} {c : M}
    (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const M ‖f c‖) U := by
  set V := {z ∈ U | ‖f z‖ = ‖f c‖}
  suffices U ⊆ V from fun x hx ↦ (this hx).2
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun x hx ↦ inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz ↦ (hm hz).out.trans_eq hx.2.symm
    replace hd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℂ, F) f y :=
      (eventually_mem_nhds_iff.2 (ho.mem_nhds hx.1)).mono fun z ↦ hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ ↦
      (Eq.trans · hx.2)
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U ∩ {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U ⊆ V ∪ W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
theorem eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace ℝ F] {f : M → F} {U : Set M}
    {c : M} (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const M (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  have hd' : MDifferentiableOn I 𝓘(ℂ, F) (f · + f c) U := fun x hx ↦
    ⟨(hd x hx).1.add continuousWithinAt_const, (hd x hx).2.add_const _⟩
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]
theorem apply_eq_of_isPreconnected_isCompact_isOpen {f : M → F} {U : Set M} {a b : M}
    (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hpc : IsPreconnected U) (hc : IsCompact U)
    (ho : IsOpen U) (ha : a ∈ U) (hb : b ∈ U) : f a = f b := by
  refine ?_
  wlog hb₀ : f b = 0 generalizing f
  · have hd' : MDifferentiableOn I 𝓘(ℂ, F) (f · - f b) U := fun x hx ↦
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : ∀ x ∈ U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀, ← norm_eq_zero, this a ha, ← this b hb, hb₀, norm_zero]
end MDifferentiableOn
namespace MDifferentiable
variable [CompactSpace M]
protected theorem isLocallyConstant {f : M → F} (hf : MDifferentiable I 𝓘(ℂ, F) f) :
    IsLocallyConstant f :=
  haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb ↦
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha
theorem apply_eq_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I 𝓘(ℂ, F) f) (a b : M) : f a = f b :=
  hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _
theorem exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I 𝓘(ℂ, F) f) : ∃ v : F, f = Function.const M v :=
  hf.isLocallyConstant.exists_eq_const
end MDifferentiable