import Mathlib.Analysis.Calculus.MeanValue
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]
open Filter Set Metric ContinuousLinearMap
open scoped Topology
theorem hasFDerivWithinAt_closure_of_tendsto_fderiv {f : E → F} {s : Set E} {x : E} {f' : E →L[ℝ] F}
    (f_diff : DifferentiableOn ℝ f s) (s_conv : Convex ℝ s) (s_open : IsOpen s)
    (f_cont : ∀ y ∈ closure s, ContinuousWithinAt f s y)
    (h : Tendsto (fun y => fderiv ℝ f y) (𝓝[s] x) (𝓝 f')) :
    HasFDerivWithinAt f f' (closure s) x := by
  classical
    by_cases hx : x ∉ closure s
    · rw [← closure_closure] at hx; exact hasFDerivWithinAt_of_nmem_closure hx
    push_neg at hx
    rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ y ∈ s, dist y x < δ → ‖fderiv ℝ f y - f'‖ < ε := by
      simpa [dist_zero_right] using tendsto_nhdsWithin_nhds.1 h ε ε_pos
    set B := ball x δ
    suffices ∀ y ∈ B ∩ closure s, ‖f y - f x - (f' y - f' x)‖ ≤ ε * ‖y - x‖ from
      mem_nhdsWithin_iff.2 ⟨δ, δ_pos, fun y hy => by simpa using this y hy⟩
    suffices
      ∀ p : E × E,
        p ∈ closure ((B ∩ s) ×ˢ (B ∩ s)) → ‖f p.2 - f p.1 - (f' p.2 - f' p.1)‖ ≤ ε * ‖p.2 - p.1‖ by
      rw [closure_prod_eq] at this
      intro y y_in
      apply this ⟨x, y⟩
      have : B ∩ closure s ⊆ closure (B ∩ s) := isOpen_ball.inter_closure
      exact ⟨this ⟨mem_ball_self δ_pos, hx⟩, this y_in⟩
    have key : ∀ p : E × E, p ∈ (B ∩ s) ×ˢ (B ∩ s) →
          ‖f p.2 - f p.1 - (f' p.2 - f' p.1)‖ ≤ ε * ‖p.2 - p.1‖ := by
      rintro ⟨u, v⟩ ⟨u_in, v_in⟩
      have conv : Convex ℝ (B ∩ s) := (convex_ball _ _).inter s_conv
      have diff : DifferentiableOn ℝ f (B ∩ s) := f_diff.mono inter_subset_right
      have bound : ∀ z ∈ B ∩ s, ‖fderivWithin ℝ f (B ∩ s) z - f'‖ ≤ ε := by
        intro z z_in
        have h := hδ z
        have : fderivWithin ℝ f (B ∩ s) z = fderiv ℝ f z := by
          have op : IsOpen (B ∩ s) := isOpen_ball.inter s_open
          rw [DifferentiableAt.fderivWithin _ (op.uniqueDiffOn z z_in)]
          exact (diff z z_in).differentiableAt (IsOpen.mem_nhds op z_in)
        rw [← this] at h
        exact le_of_lt (h z_in.2 z_in.1)
      simpa using conv.norm_image_sub_le_of_norm_fderivWithin_le' diff bound u_in v_in
    rintro ⟨u, v⟩ uv_in
    have f_cont' : ∀ y ∈ closure s, ContinuousWithinAt (f -  ⇑f') s y := by
      intro y y_in
      exact Tendsto.sub (f_cont y y_in) f'.cont.continuousWithinAt
    refine ContinuousWithinAt.closure_le uv_in ?_ ?_ key
    all_goals
      have : (B ∩ s) ×ˢ (B ∩ s) ⊆ s ×ˢ s := by gcongr <;> exact inter_subset_right
      obtain ⟨u_in, v_in⟩ : u ∈ closure s ∧ v ∈ closure s := by
        simpa [closure_prod_eq] using closure_mono this uv_in
      apply ContinuousWithinAt.mono _ this
      simp only [ContinuousWithinAt]
    · rw [nhdsWithin_prod_eq]
      have : ∀ u v, f v - f u - (f' v - f' u) = f v - f' v - (f u - f' u) := by intros; abel
      simp only [this]
      exact
        Tendsto.comp continuous_norm.continuousAt
          ((Tendsto.comp (f_cont' v v_in) tendsto_snd).sub <|
            Tendsto.comp (f_cont' u u_in) tendsto_fst)
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      rw [nhds_prod_eq]
      exact
        tendsto_const_nhds.mul
          (Tendsto.comp continuous_norm.continuousAt <| tendsto_snd.sub tendsto_fst)
@[deprecated (since := "2024-07-10")] alias has_fderiv_at_boundary_of_tendsto_fderiv :=
  hasFDerivWithinAt_closure_of_tendsto_fderiv
theorem hasDerivWithinAt_Ici_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
    (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a) (hs : s ∈ 𝓝[>] a)
    (f_lim' : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)) : HasDerivWithinAt f e (Ici a) a := by
  obtain ⟨b, ab : a < b, sab : Ioc a b ⊆ s⟩ := mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 hs
  let t := Ioo a b
  have ts : t ⊆ s := Subset.trans Ioo_subset_Ioc_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo a b
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc a b := closure_Ioo ab.ne
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y := by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨lt_of_le_of_ne hy.1 (Ne.symm h), hy.2⟩
      exact (f_diff.continuousOn y this).mono ts
  have t_diff' : Tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smulRight (1 : ℝ →L[ℝ] ℝ) e)) := by
    simp only [deriv_fderiv.symm]
    exact Tendsto.comp
      (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.continuousAt
      (tendsto_nhdsWithin_mono_left Ioo_subset_Ioi_self f_lim')
  have : HasDerivWithinAt f e (Icc a b) a := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Ici <| left_mem_Ico.2 ab)
@[deprecated (since := "2024-07-10")] alias has_deriv_at_interval_left_endpoint_of_tendsto_deriv :=
  hasDerivWithinAt_Ici_of_tendsto_deriv
theorem hasDerivWithinAt_Iic_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ}
    {f : ℝ → E} (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a)
    (hs : s ∈ 𝓝[<] a) (f_lim' : Tendsto (fun x => deriv f x) (𝓝[<] a) (𝓝 e)) :
    HasDerivWithinAt f e (Iic a) a := by
  obtain ⟨b, ba, sab⟩ : ∃ b ∈ Iio a, Ico b a ⊆ s := mem_nhdsWithin_Iio_iff_exists_Ico_subset.1 hs
  let t := Ioo b a
  have ts : t ⊆ s := Subset.trans Ioo_subset_Ico_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo b a
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc b a := closure_Ioo (ne_of_lt ba)
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y := by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩
      exact (f_diff.continuousOn y this).mono ts
  have t_diff' : Tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smulRight (1 : ℝ →L[ℝ] ℝ) e)) := by
    simp only [deriv_fderiv.symm]
    exact Tendsto.comp
      (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.continuousAt
      (tendsto_nhdsWithin_mono_left Ioo_subset_Iio_self f_lim')
  have : HasDerivWithinAt f e (Icc b a) a := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Iic <| right_mem_Ioc.2 ba)
@[deprecated (since := "2024-07-10")] alias has_deriv_at_interval_right_endpoint_of_tendsto_deriv :=
  hasDerivWithinAt_Iic_of_tendsto_deriv
theorem hasDerivAt_of_hasDerivAt_of_ne {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ y ≠ x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x := by
  have A : HasDerivWithinAt f (g x) (Ici x) x := by
    have diff : DifferentiableOn ℝ f (Ioi x) := fun y hy =>
      (f_diff y (ne_of_gt hy)).differentiableAt.differentiableWithinAt
    apply
      hasDerivWithinAt_Ici_of_tendsto_deriv diff hf.continuousWithinAt
        self_mem_nhdsWithin
    have : Tendsto g (𝓝[>] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    intros y hy
    exact (f_diff y (ne_of_gt hy)).deriv.symm
  have B : HasDerivWithinAt f (g x) (Iic x) x := by
    have diff : DifferentiableOn ℝ f (Iio x) := fun y hy =>
      (f_diff y (ne_of_lt hy)).differentiableAt.differentiableWithinAt
    apply
      hasDerivWithinAt_Iic_of_tendsto_deriv diff hf.continuousWithinAt
        self_mem_nhdsWithin
    have : Tendsto g (𝓝[<] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    intros y hy
    exact (f_diff y (ne_of_lt hy)).deriv.symm
  simpa using B.union A
theorem hasDerivAt_of_hasDerivAt_of_ne' {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ y ≠ x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (y : ℝ) : HasDerivAt f (g y) y := by
  rcases eq_or_ne y x with (rfl | hne)
  · exact hasDerivAt_of_hasDerivAt_of_ne f_diff hf hg
  · exact f_diff y hne