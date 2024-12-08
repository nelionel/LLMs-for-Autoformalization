import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.PartialHomeomorph
open Function Set Filter Metric
open scoped Topology NNReal
noncomputable section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ε : ℝ}
open Filter Metric Set
open ContinuousLinearMap (id)
def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c : ℝ≥0) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖
@[simp]
theorem approximatesLinearOn_empty (f : E → F) (f' : E →L[𝕜] F) (c : ℝ≥0) :
    ApproximatesLinearOn f f' ∅ c := by simp [ApproximatesLinearOn]
namespace ApproximatesLinearOn
variable {f : E → F}
section
variable {f' : E →L[𝕜] F} {s t : Set E} {c c' : ℝ≥0}
theorem mono_num (hc : c ≤ c') (hf : ApproximatesLinearOn f f' s c) :
    ApproximatesLinearOn f f' s c' := fun x hx y hy =>
  le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc <| norm_nonneg _)
theorem mono_set (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) :
    ApproximatesLinearOn f f' s c := fun x hx y hy => hf x (hst hx) y (hst hy)
theorem approximatesLinearOn_iff_lipschitzOnWith {f : E → F} {f' : E →L[𝕜] F} {s : Set E}
    {c : ℝ≥0} : ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f - ⇑f') s := by
  have : ∀ x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := fun x y ↦ by
    simp only [map_sub, Pi.sub_apply]; abel
  simp only [this, lipschitzOnWith_iff_norm_sub_le, ApproximatesLinearOn]
alias ⟨lipschitzOnWith, _root_.LipschitzOnWith.approximatesLinearOn⟩ :=
  approximatesLinearOn_iff_lipschitzOnWith
theorem lipschitz_sub (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith c fun x : s => f x - f' x :=
  hf.lipschitzOnWith.to_restrict
protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith (‖f'‖₊ + c) (s.restrict f) := by
  simpa only [restrict_apply, add_sub_cancel] using
    (f'.lipschitz.restrict s).add hf.lipschitz_sub
protected theorem continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.restrict f) :=
  hf.lipschitz.continuous
protected theorem continuousOn (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuousOn_iff_continuous_restrict.2 hf.continuous
end
section LocallyOnto
variable [CompleteSpace E] {s : Set E} {c : ℝ≥0} {f' : E →L[𝕜] F}
theorem surjOn_closedBall_of_nonlinearRightInverse
    (hf : ApproximatesLinearOn f f' s c)
    (f'symm : f'.NonlinearRightInverse) {ε : ℝ} {b : E} (ε0 : 0 ≤ ε) (hε : closedBall b ε ⊆ s) :
    SurjOn f (closedBall b ε) (closedBall (f b) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε)) := by
  intro y hy
  rcases le_or_lt (f'symm.nnnorm : ℝ)⁻¹ c with hc | hc
  · refine ⟨b, by simp [ε0], ?_⟩
    have : dist y (f b) ≤ 0 :=
      (mem_closedBall.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : ℝ) < f'symm.nnnorm := by rw [← inv_pos]; exact (NNReal.coe_nonneg _).trans_lt hc
  have Icf' : (c : ℝ) * f'symm.nnnorm < 1 := by rwa [inv_eq_one_div, lt_div_iff₀ If'] at hc
  have Jf' : (f'symm.nnnorm : ℝ) ≠ 0 := ne_of_gt If'
  have Jcf' : (1 : ℝ) - c * f'symm.nnnorm ≠ 0 := by apply ne_of_gt; linarith
  set g := fun x => x + f'symm (y - f x) with hg
  set u := fun n : ℕ => g^[n] b with hu
  have usucc : ∀ n, u (n + 1) = g (u n) := by simp [hu, ← iterate_succ_apply' g _ b]
  have A : ∀ z, dist (g z) z ≤ f'symm.nnnorm * dist (f z) y := by
    intro z
    rw [dist_eq_norm, hg, add_sub_cancel_left, dist_eq_norm']
    exact f'symm.bound _
  have B :
    ∀ z ∈ closedBall b ε,
      g z ∈ closedBall b ε → dist (f (g z)) y ≤ c * f'symm.nnnorm * dist (f z) y := by
    intro z hz hgz
    set v := f'symm (y - f z)
    calc
      dist (f (g z)) y = ‖f (z + v) - y‖ := by rw [dist_eq_norm]
      _ = ‖f (z + v) - f z - f' v + f' v - (y - f z)‖ := by congr 1; abel
      _ = ‖f (z + v) - f z - f' (z + v - z)‖ := by
        simp only [v, ContinuousLinearMap.NonlinearRightInverse.right_inv, add_sub_cancel_left,
          sub_add_cancel]
      _ ≤ c * ‖z + v - z‖ := hf _ (hε hgz) _ (hε hz)
      _ ≤ c * (f'symm.nnnorm * dist (f z) y) := by
        gcongr
        simpa [dist_eq_norm'] using f'symm.bound (y - f z)
      _ = c * f'symm.nnnorm * dist (f z) y := by ring
  have C : ∀ (n : ℕ) (w : E), dist w b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) /
      (1 - c * f'symm.nnnorm) * dist (f b) y → w ∈ closedBall b ε := fun n w hw ↦ by
    apply hw.trans
    rw [div_mul_eq_mul_div, div_le_iff₀]; swap; · linarith
    calc
      (f'symm.nnnorm : ℝ) * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) * dist (f b) y =
          f'symm.nnnorm * dist (f b) y * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) := by
        ring
      _ ≤ f'symm.nnnorm * dist (f b) y * 1 := by
        gcongr
        rw [sub_le_self_iff]
        positivity
      _ ≤ f'symm.nnnorm * (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε) := by
        rw [mul_one]
        gcongr
        exact mem_closedBall'.1 hy
      _ = ε * (1 - c * f'symm.nnnorm) := by field_simp; ring
  have D : ∀ n : ℕ, dist (f (u n)) y ≤ ((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y ∧
      dist (u n) b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) /
        (1 - (c : ℝ) * f'symm.nnnorm) * dist (f b) y := fun n ↦ by
    induction' n with n IH; · simp [hu, le_refl]
    rw [usucc]
    have Ign : dist (g (u n)) b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n.succ) /
        (1 - c * f'symm.nnnorm) * dist (f b) y :=
      calc
        dist (g (u n)) b ≤ dist (g (u n)) (u n) + dist (u n) b := dist_triangle _ _ _
        _ ≤ f'symm.nnnorm * dist (f (u n)) y + dist (u n) b := add_le_add (A _) le_rfl
        _ ≤ f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) +
              f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) *
                dist (f b) y := by
                  gcongr
                  · exact IH.1
                  · exact IH.2
        _ = f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n.succ) /
              (1 - (c : ℝ) * f'symm.nnnorm) * dist (f b) y := by
          field_simp [Jcf', pow_succ]; ring
    refine ⟨?_, Ign⟩
    calc
      dist (f (g (u n))) y ≤ c * f'symm.nnnorm * dist (f (u n)) y :=
        B _ (C n _ IH.2) (C n.succ _ Ign)
      _ ≤ (c : ℝ) * f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        apply IH.1
      _ = ((c : ℝ) * f'symm.nnnorm) ^ n.succ * dist (f b) y := by simp only [pow_succ']; ring
  have : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ (↑f'symm.nnnorm * dist (f b) y) Icf' fun n ↦ ?_
    calc
      dist (u n) (u (n + 1)) = dist (g (u n)) (u n) := by rw [usucc, dist_comm]
      _ ≤ f'symm.nnnorm * dist (f (u n)) y := A _
      _ ≤ f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        exact (D n).1
      _ = f'symm.nnnorm * dist (f b) y * ((c : ℝ) * f'symm.nnnorm) ^ n := by ring
  obtain ⟨x, hx⟩ : ∃ x, Tendsto u atTop (𝓝 x) := cauchySeq_tendsto_of_complete this
  have xmem : x ∈ closedBall b ε :=
    isClosed_ball.mem_of_tendsto hx (Eventually.of_forall fun n => C n _ (D n).2)
  refine ⟨x, xmem, ?_⟩
  have hx' : Tendsto u atTop (𝓝[closedBall b ε] x) := by
    simp only [nhdsWithin, tendsto_inf, hx, true_and, tendsto_principal]
    exact Eventually.of_forall fun n => C n _ (D n).2
  have T1 : Tendsto (f ∘ u) atTop (𝓝 (f x)) :=
    (hf.continuousOn.mono hε x xmem).tendsto.comp hx'
  have T2 : Tendsto (f ∘ u) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (D n).1) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) Icf').mul tendsto_const_nhds
  exact tendsto_nhds_unique T1 T2
theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    (hs : IsOpen s) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) := by
  cases' hc with hE hc
  · exact isOpen_discrete _
  simp only [isOpen_iff_mem_nhds, nhds_basis_closedBall.mem_iff, forall_mem_image] at hs ⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, ?_⟩
  exact (hf.surjOn_closedBall_of_nonlinearRightInverse f'symm (le_of_lt ε0) hε).mono hε Subset.rfl
theorem image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    {x : E} (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : f '' s ∈ 𝓝 (f x) := by
  obtain ⟨t, hts, ht, xt⟩ : ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := _root_.mem_nhds_iff.1 hs
  have := IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)
  exact mem_of_superset this (image_subset _ hts)
theorem map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
    (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : map f (𝓝 x) = 𝓝 (f x) := by
  refine
    le_antisymm ((hf.continuousOn x (mem_of_mem_nhds hs)).continuousAt hs) (le_map fun t ht => ?_)
  have : f '' (s ∩ t) ∈ 𝓝 (f x) :=
    (hf.mono_set inter_subset_left).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_subset _ inter_subset_right)
end LocallyOnto
variable {f' : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0}
local notation "N" => ‖(f'.symm : F →L[𝕜] E)‖₊
protected theorem antilipschitz (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : AntilipschitzWith (N⁻¹ - c)⁻¹ (s.restrict f) := by
  cases' hc with hE hc
  · exact AntilipschitzWith.of_subsingleton
  convert (f'.antilipschitz.restrict s).add_lipschitzWith hf.lipschitz_sub hc
  simp [restrict]
protected theorem injective (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Injective (s.restrict f) :=
  (hf.antilipschitz hc).injective
protected theorem injOn (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : InjOn f s :=
  injOn_iff_injective.2 <| hf.injective hc
protected theorem surjective [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Surjective f := by
  cases' hc with hE hc
  · haveI : Subsingleton F := (Equiv.subsingleton_congr f'.toEquiv).1 hE
    exact surjective_to_subsingleton _
  · apply forall_of_forall_mem_closedBall (fun y : F => ∃ a, f a = y) (f 0) _
    have hc' : (0 : ℝ) < N⁻¹ - c := by rw [sub_pos]; exact hc
    let p : ℝ → Prop := fun R => closedBall (f 0) R ⊆ Set.range f
    have hp : ∀ᶠ r : ℝ in atTop, p ((N⁻¹ - c) * r) := by
      have hr : ∀ᶠ r : ℝ in atTop, 0 ≤ r := eventually_ge_atTop 0
      refine hr.mono fun r hr => Subset.trans ?_ (image_subset_range f (closedBall 0 r))
      refine hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse hr ?_
      exact subset_univ _
    refine ((tendsto_id.const_mul_atTop hc').frequently hp.frequently).mono ?_
    exact fun R h y hy => h hy
def toPartialEquiv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : PartialEquiv E F :=
  (hf.injOn hc).toPartialEquiv _ _
theorem inverse_continuousOn (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : ContinuousOn (hf.toPartialEquiv hc).symm (f '' s) := by
  apply continuousOn_iff_continuous_restrict.2
  refine ((hf.antilipschitz hc).to_rightInvOn' ?_ (hf.toPartialEquiv hc).right_inv').continuous
  exact fun x hx => (hf.toPartialEquiv hc).map_target hx
theorem to_inv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    ApproximatesLinearOn (hf.toPartialEquiv hc).symm (f'.symm : F →L[𝕜] E) (f '' s)
      (N * (N⁻¹ - c)⁻¹ * c) := fun x hx y hy ↦ by
  set A := hf.toPartialEquiv hc
  have Af : ∀ z, A z = f z := fun z => rfl
  rcases (mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases (mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x', ← Af y', A.left_inv x's, A.left_inv y's]
  calc
    ‖x' - y' - f'.symm (A x' - A y')‖ ≤ N * ‖f' (x' - y' - f'.symm (A x' - A y'))‖ :=
      (f' : E →L[𝕜] F).bound_of_antilipschitz f'.antilipschitz _
    _ = N * ‖A y' - A x' - f' (y' - x')‖ := by
      congr 2
      simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.map_sub]
      abel
    _ ≤ N * (c * ‖y' - x'‖) := mul_le_mul_of_nonneg_left (hf _ y's _ x's) (NNReal.coe_nonneg _)
    _ ≤ N * (c * (((N⁻¹ - c)⁻¹ : ℝ≥0) * ‖A y' - A x'‖)) := by
      gcongr
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact (hf.antilipschitz hc).le_mul_dist ⟨y', y's⟩ ⟨x', x's⟩
    _ = (N * (N⁻¹ - c)⁻¹ * c : ℝ≥0) * ‖A x' - A y'‖ := by
      simp only [norm_sub_rev, NNReal.coe_mul]; ring
variable [CompleteSpace E]
section
variable (f s)
def toPartialHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : PartialHomeomorph E F where
  toPartialEquiv := hf.toPartialEquiv hc
  open_source := hs
  open_target := hf.open_image f'.toNonlinearRightInverse hs <| by
    rwa [f'.toEquiv.subsingleton_congr] at hc
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hf.inverse_continuousOn hc
@[simp]
theorem toPartialHomeomorph_coe (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toPartialHomeomorph f s hc hs : E → F) = f :=
  rfl
@[simp]
theorem toPartialHomeomorph_source (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toPartialHomeomorph f s hc hs).source = s :=
  rfl
@[simp]
theorem toPartialHomeomorph_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toPartialHomeomorph f s hc hs).target = f '' s :=
  rfl
def toHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : E ≃ₜ F := by
  refine (hf.toPartialHomeomorph _ _ hc isOpen_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl ?_
  rw [toPartialHomeomorph_target, image_univ, range_eq_univ]
  exact hf.surjective hc
end
theorem closedBall_subset_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) {b : E} (ε0 : 0 ≤ ε) (hε : closedBall b ε ⊆ s) :
    closedBall (f b) ((N⁻¹ - c) * ε) ⊆ (hf.toPartialHomeomorph f s hc hs).target :=
  (hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse ε0 hε).mono hε
    Subset.rfl
end ApproximatesLinearOn