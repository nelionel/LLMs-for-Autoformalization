import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Metric Set Asymptotics Filter Real
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def gronwallBound (δ K ε x : ℝ) : ℝ :=
  if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)
theorem gronwallBound_K0 (δ ε : ℝ) : gronwallBound δ 0 ε = fun x => δ + ε * x :=
  funext fun _ => if_pos rfl
theorem gronwallBound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
    gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1) :=
  funext fun _ => if_neg hK
theorem hasDerivAt_gronwallBound (δ K ε x : ℝ) :
    HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
      ((((hasDerivAt_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1
    simp only [id, mul_add, (mul_assoc _ _ _).symm, mul_comm _ K, mul_div_cancel₀ _ hK]
    ring
theorem hasDerivAt_gronwallBound_shift (δ K ε x a : ℝ) :
    HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x := by
  convert (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id, mul_one]
theorem gronwallBound_x0 (δ K ε : ℝ) : gronwallBound δ K ε 0 = δ := by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]
theorem gronwallBound_ε0 (δ K x : ℝ) : gronwallBound δ K 0 x = δ * exp (K * x) := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]
theorem gronwallBound_ε0_δ0 (K x : ℝ) : gronwallBound 0 K 0 x = 0 := by
  simp only [gronwallBound_ε0, zero_mul]
theorem gronwallBound_continuous_ε (δ K x : ℝ) : Continuous fun ε => gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    exact continuous_const.add (continuous_id.mul continuous_const)
  · simp only [gronwallBound_of_K_ne_0 hK]
    exact continuous_const.add ((continuous_id.mul continuous_const).mul continuous_const)
theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε) :
    ∀ x ∈ Icc a b, f x ≤ gronwallBound δ K ε (x - a) := by
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioi ε, f x ≤ gronwallBound δ K ε' (x - a) := by
    intro x hx ε' hε'
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
    · intro x hx hfB
      rw [← hfB]
      apply lt_of_le_of_lt (bound x hx)
      exact add_lt_add_left (mem_Ioi.1 hε') _
    · exact hx
  intro x hx
  change f x ≤ (fun ε' => gronwallBound δ K ε' (x - a)) ε
  convert continuousWithinAt_const.closure_le _ _ (H x hx)
  · simp only [closure_Ioi, left_mem_Ici]
  exact (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt
theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound
variable {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g f' g' : ℝ → E} {a b t₀ : ℝ} {εf εg δ : ℝ}
  (hv : ∀ t, LipschitzOnWith K (v t) (s t))
include hv in
theorem dist_le_of_approx_trajectories_ODE_of_mem
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) := by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))
  have hv := (hv t).dist_le_mul _ (hfs t ht) _ (hgs t ht)
  rw [← dist_eq_norm, ← dist_eq_norm]
  refine this.trans ((add_le_add (add_le_add (f_bound t ht) (g_bound t ht)) hv).trans ?_)
  rw [add_comm]
theorem dist_le_of_approx_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha
include hv in
theorem dist_le_of_trajectories_ODE_of_mem
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) := by
  have f_bound : ∀ t ∈ Ico a b, dist (v t (f t)) (v t (f t)) ≤ 0 := by intros; rw [dist_self]
  have g_bound : ∀ t ∈ Ico a b, dist (v t (g t)) (v t (g t)) ≤ 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this
theorem dist_le_of_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha
include hv in
theorem ODE_solution_unique_of_mem_Icc_right
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this
include hv in
theorem ODE_solution_unique_of_mem_Icc_left
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioc a b, HasDerivWithinAt f (v t (f t)) (Iic t) t)
    (hfs : ∀ t ∈ Ioc a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioc a b, HasDerivWithinAt g (v t (g t)) (Iic t) t)
    (hgs : ∀ t ∈ Ioc a b, g t ∈ s t)
    (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  have hv' t : LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _)
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht ↦ ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht ↦ ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt3 (t : ℝ) : MapsTo Neg.neg (Ici t) (Iic (-t)) :=
    fun _ ht' ↦ mem_Iic.mpr <| neg_le_neg ht'
  suffices EqOn (f ∘ Neg.neg) (g ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at this
    convert this
    simp
  apply ODE_solution_unique_of_mem_Icc_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hgs _ (hmt2 ht)) (by simp [hb])
  · intros t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp
  · intros t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp
include hv in
theorem ODE_solution_unique_of_mem_Icc
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ ⊆ Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left hv
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq
  · have hss : Ico t₀ b ⊆ Ioo a b := Ico_subset_Ioo_left ht.1
    exact ODE_solution_unique_of_mem_Icc_right hv
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq
include hv in
theorem ODE_solution_unique_of_mem_Ioo
    (ht : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  intros t' ht'
  rcases lt_or_le t' t₀ with (h | h)
  · have hss : Icc t' t₀ ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left hv
      (continuousOn_of_forall_continuousAt fun _ ht'' ↦ (hf _ <| hss ht'').1.continuousAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').2)
      (continuousOn_of_forall_continuousAt fun _ ht'' ↦ (hg _ <| hss ht'').1.continuousAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').2) heq
      ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t' ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht.1 ht''.1, lt_of_le_of_lt ht''.2 ht'.2⟩
    exact ODE_solution_unique_of_mem_Icc_right hv
      (continuousOn_of_forall_continuousAt fun _ ht'' ↦ (hf _ <| hss ht'').1.continuousAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').2)
      (continuousOn_of_forall_continuousAt fun _ ht'' ↦ (hg _ <| hss ht'').1.continuousAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').2) heq
      ⟨h, le_rfl⟩
include hv in
theorem ODE_solution_unique_of_eventually
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hf.and hg)
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo hv (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_self hε)
    (fun _ ht ↦ (h _ ht).1) (fun _ ht ↦ (h _ ht).2) heq
theorem ODE_solution_unique
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha