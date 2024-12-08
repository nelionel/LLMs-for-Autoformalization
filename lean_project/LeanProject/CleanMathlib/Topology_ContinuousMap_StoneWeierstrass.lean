import Mathlib.Algebra.Algebra.Subalgebra.Unitization
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.Lattice
noncomputable section
namespace ContinuousMap
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
open scoped Polynomial
def attachBound (f : C(X, ℝ)) : C(X, Set.Icc (-‖f‖) ‖f‖) where
  toFun x := ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩
@[simp]
theorem attachBound_apply_coe (f : C(X, ℝ)) (x : X) : ((attachBound f) x : ℝ) = f x :=
  rfl
theorem polynomial_comp_attachBound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound =
      Polynomial.aeval f g := by
  ext
  simp only [ContinuousMap.coe_comp, Function.comp_apply, ContinuousMap.attachBound_apply_coe,
    Polynomial.toContinuousMapOn_apply, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_continuousMap_apply, Polynomial.toContinuousMap_apply]
  erw [ContinuousMap.attachBound_apply_coe]
theorem polynomial_comp_attachBound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem
theorem comp_attachBound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A)
    (p : C(Set.Icc (-‖f‖) ‖f‖, ℝ)) : p.comp (attachBound (f : C(X, ℝ))) ∈ A.topologicalClosure := by
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  apply mem_closure_iff_frequently.mpr
  refine
    ((compRightContinuousMap ℝ (attachBound (f : C(X, ℝ)))).continuousAt
            p).tendsto.frequently_map
      _ ?_ frequently_mem_polynomials
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_toRingHom, compRightContinuousMap_apply,
    Polynomial.toContinuousMapOnAlgHom_apply]
  apply polynomial_comp_attachBound_mem
theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) :
    |(f : C(X, ℝ))| ∈ A.topologicalClosure := by
  let f' := attachBound (f : C(X, ℝ))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, ℝ) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : ℝ)| }
  change abs.comp f' ∈ A.topologicalClosure
  apply comp_attachBound_mem_closure
theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _
theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A := by
  convert inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_isClosed]
  exact h
theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _
theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A := by
  convert sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_isClosed]
  exact h
open scoped Topology
theorem sublattice_closure_eq_top (L : Set C(X, ℝ)) (nA : L.Nonempty)
    (inf_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊓ g ∈ L)
    (sup_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊔ g ∈ L) (sep : L.SeparatesPointsStrongly) :
    closure L = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [exists_prop, Metric.mem_ball]
  by_cases nX : Nonempty X
  swap
  · exact ⟨nA.some, (dist_lt_iff pos).mpr fun x => False.elim (nX ⟨x⟩), nA.choose_spec⟩
  dsimp only [Set.SeparatesPointsStrongly] at sep
  choose g hg w₁ w₂ using sep f
  let U : X → X → Set X := fun x y => {z | f z - ε < g x y z}
  have U_nhd_y : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> continuity
    · rw [Set.mem_setOf_eq, w₂]
      exact sub_lt_self _ pos
  let ys : X → Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).choose
  let ys_w : ∀ x, ⋃ y ∈ ys x, U x y = ⊤ := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).choose_spec
  have ys_nonempty : ∀ x, (ys x).Nonempty := fun x =>
    Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  let h : X → L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, ℝ)),
      Finset.sup'_mem _ sup_mem _ _ _ fun y _ => hg x y⟩
  have lt_h : ∀ x z, f z - ε < (h x : X → ℝ) z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp
    simp only [Subtype.coe_mk, coe_sup', Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : ∀ x, (h x : X → ℝ) x = f x := by intro x; simp [w₁]
  let W : X → Set X := fun x => {z | (h x : X → ℝ) z < f z + ε}
  have W_nhd : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · dsimp only [W, Set.mem_setOf_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ pos
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhd).choose
  let xs_w : ⋃ x ∈ xs, W x = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhd).choose_spec
  have xs_nonempty : xs.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, ℝ)),
      Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine ⟨k.1, ?_, k.2⟩
  rw [dist_lt_iff pos]
  intro z
  rw [show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a by
        intros; simp only [← Metric.mem_ball, Real.ball_eq_Ioo, Set.mem_Ioo, and_comm]]
  fconstructor
  · dsimp
    simp only [Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
  · dsimp
    simp only [Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    rintro x -
    apply lt_h
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.le_topologicalClosure A.one_mem⟩
  convert
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly
        (Subalgebra.separatesPoints_monotone A.le_topologicalClosure w))
  simp [L]
theorem continuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) : f ∈ A.topologicalClosure := by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp
theorem exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ‖(g : C(X, ℝ)) - f‖ < ε := by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩
theorem exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ∀ x, ‖(g : X → ℝ) x - f x‖ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b
end ContinuousMap
section RCLike
open RCLike
variable {𝕜 : Type*} {X : Type*} [RCLike 𝕜] [TopologicalSpace X]
open ContinuousMap
theorem Subalgebra.SeparatesPoints.rclike_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)}
    (hA : A.SeparatesPoints) :
      ((A.restrictScalars ℝ).comap
        (ofRealAm.compLeftContinuous ℝ continuous_ofReal)).SeparatesPoints := by
  intro x₁ x₂ hx
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  have hFA : F ∈ A := by
    refine A.sub_mem hfA (@Eq.subst _ (· ∈ A) _ _ ?_ <| A.smul_mem A.one_mem <| f x₂)
    ext1
    simp only [coe_smul, coe_one, smul_apply, one_apply, Algebra.id.smul_eq_mul, mul_one,
      const_apply]
  refine ⟨_, ⟨⟨(‖F ·‖ ^ 2), by continuity⟩, ?_, rfl⟩, ?_⟩
  · 
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert (A.restrictScalars ℝ).mul_mem hFA (star_mem hFA : star F ∈ A)
    ext1
    simp [← RCLike.mul_conj]
  · 
    simpa [F] using sub_ne_zero.mpr hf
variable [CompactSpace X]
theorem ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  rw [StarSubalgebra.eq_top_iff]
  let I : C(X, ℝ) →ₗ[ℝ] C(X, 𝕜) := ofRealCLM.compLeftContinuous ℝ X
  have key : LinearMap.range I ≤ (A.toSubmodule.restrictScalars ℝ).topologicalClosure := by
    let A₀ : Submodule ℝ C(X, ℝ) := (A.toSubmodule.restrictScalars ℝ).comap I
    have SW : A₀.topologicalClosure = ⊤ :=
      haveI := subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hA.rclike_to_real
      congr_arg Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    have h₁ := A₀.topologicalClosure_map ((@ofRealCLM 𝕜 _).compLeftContinuousCompact X)
    have h₂ := (A.toSubmodule.restrictScalars ℝ).map_comap_le I
    exact h₁.trans (Submodule.topologicalClosure_mono h₂)
  intro f
  let f_re : C(X, ℝ) := (⟨RCLike.re, RCLike.reCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨RCLike.im, RCLike.imCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topologicalClosure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topologicalClosure := key ⟨f_im, rfl⟩
  have := A.topologicalClosure.add_mem h_f_re (A.topologicalClosure.smul_mem h_f_im RCLike.I)
  rw [StarSubalgebra.mem_toSubalgebra] at this
  convert this
  ext
  apply Eq.symm
  simp [I, f_re, f_im, mul_comm RCLike.I _]
end RCLike
section PolynomialFunctions
open StarSubalgebra Polynomial
open scoped Polynomial
theorem polynomialFunctions.topologicalClosure (s : Set ℝ)
    [CompactSpace s] : (polynomialFunctions s).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)
theorem polynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜)
    [CompactSpace s] : (polynomialFunctions s).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))
@[elab_as_elim]
theorem ContinuousMap.induction_on {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜}
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (closure : (∀ f ∈ (polynomialFunctions s).starClosure, p f) → ∀ f, p f) (f : C(s, 𝕜)) :
    p f := by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_star] at hf
    rw [star_eq_iff_star_eq, eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id]
  | algebraMap r => exact const r
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
open Topology in
@[elab_as_elim]
theorem ContinuousMap.induction_on_of_compact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s]
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)) :
    p f := by
  refine f.induction_on const id star_id add mul fun h f ↦ frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe, topologicalClosure_coe, mem_closure_iff_frequently] at this
  exact this.mp <| .of_forall h
@[ext (iff := false)]
theorem ContinuousMap.algHom_ext_map_X {A : Type*} [Ring A]
    [Algebra ℝ A] [TopologicalSpace A] [T2Space A] {s : Set ℝ} [CompactSpace s]
    {φ ψ : C(s, ℝ) →ₐ[ℝ] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : Subalgebra ℝ C(s, ℝ)) ≤ AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal (polynomialFunctions s)
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)
@[ext (iff := false)]
theorem ContinuousMap.starAlgHom_ext_map_X {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
    [Algebra 𝕜 A] [TopologicalSpace A] [T2Space A] {s : Set 𝕜} [CompactSpace s]
    {φ ψ : C(s, 𝕜) →⋆ₐ[𝕜] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) ≤ StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_eq hφ hψ)
end PolynomialFunctions
section ContinuousMapZero
variable {𝕜 : Type*} [RCLike 𝕜]
open NonUnitalStarAlgebra Submodule
namespace ContinuousMap
lemma adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} ∪ (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, span_union, span_eq_toSubmodule]
open Pointwise in
lemma adjoin_id_eq_span_one_add (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) := by
  ext x
  rw [SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, mem_sup]
  simp [Set.mem_add]
lemma nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 0 ∈ s) :
    (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ⊆
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) := by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_smul, hf, smul_zero]
  | star f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_star, hf, star_zero]
lemma ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) :
    (StarAlgebra.adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ∩
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) = adjoin 𝕜 {restrict s (.id 𝕜)} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    simp only [SetLike.mem_coe, RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply, this, add_zero, smul_apply, one_apply, smul_eq_mul, mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf ↦ ⟨?_, nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf⟩
    exact adjoin_le_starAlgebra_adjoin _ _ hf
open RingHom Filter Topology in
theorem AlgHom.closure_ker_inter {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s ∩ RingHom.ker φ) = closure s ∩ (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt, ClusterPt] at hxs
    have : Tendsto (fun y ↦ y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
    refine mem_closure_of_tendsto this <| eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩
lemma ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) [CompactSpace s] :
    (RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) =
      closure (adjoin 𝕜 {(restrict s (.id 𝕜))}) := by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0,
    AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0, h0⟩) (continuous_eval_const _) _]
  convert (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id, ← Polynomial.toContinuousMapOnAlgHom_apply,
    ← polynomialFunctions.starClosure_eq_adjoin_X s]
  congrm(($(polynomialFunctions.starClosure_topologicalClosure s) : Set C(s, 𝕜)))
end ContinuousMap
open scoped ContinuousMapZero
lemma ContinuousMapZero.adjoin_id_dense {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    [CompactSpace s] : Dense (adjoin 𝕜 {(.id h0 : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀) := by
  have h0' : 0 ∈ s := h0 ▸ (0 : s).property
  rw [dense_iff_closure_eq,
    ← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _),
    ← isClosedEmbedding_toContinuousMap.closure_image_eq, ← coe_toContinuousMapHom,
    ← NonUnitalStarSubalgebra.coe_map, NonUnitalStarAlgHom.map_adjoin_singleton,
    toContinuousMapHom_apply, toContinuousMap_id h0,
    ← ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id s h0']
  apply Set.eq_univ_of_forall fun f ↦ ?_
  simp only [Set.mem_preimage, toContinuousMapHom_apply, SetLike.mem_coe, RingHom.mem_ker,
    ContinuousMap.evalStarAlgHom_apply, ContinuousMap.coe_coe]
  rw [show ⟨0, h0'⟩ = (0 : s) by ext; exact h0.symm, _root_.map_zero f]
@[elab_as_elim]
lemma ContinuousMapZero.induction_on {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id h0)) (star_id : p (star (.id h0)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (closure : (∀ f ∈ adjoin 𝕜 {(.id h0 : C(s, 𝕜)₀)}, p f) → ∀ f, p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_star] at hf
    rw [star_eq_iff_star_eq, eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
  | smul _ _ _ hf => exact smul _ _ hf
open Topology in
@[elab_as_elim]
theorem ContinuousMapZero.induction_on_of_compact {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    [CompactSpace s] {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id h0))
    (star_id : p (star (.id h0))) (add : ∀ f g, p f → p g → p (f + g))
    (mul : ∀ f g, p f → p g → p (f * g)) (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine f.induction_on h0 zero id star_id add mul smul fun h f ↦ frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense h0).closure_eq ▸ Set.mem_univ (x := f)
  exact mem_closure_iff_frequently.mp this |>.mp <| .of_forall h
lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [TopologicalSemiring A]
    [T2Space A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Zero s] [CompactSpace s]
    (h0 : (0 : s) = (0 : 𝕜)) (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id h0) * a = 0)
    (hmul_star_id : φ (star (.id h0)) * a = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    φ f * a = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact h0 with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ h => rw [map_smul, smul_mul_assoc, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero
lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [TopologicalSemiring A]
    [T2Space A] [Module 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Zero s] [CompactSpace s]
    (h0 : (0 : s) = (0 : 𝕜)) (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ (.id h0) = 0)
    (hmul_star_id : a * φ (star (.id h0)) = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    a * φ f = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact h0 with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ _ h => rw [map_smul, mul_smul_comm, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero
end ContinuousMapZero