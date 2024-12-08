import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace
open scoped NNReal ENNReal Topology Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
theorem exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      (∀ n, IsClosed (t n)) ∧
        (s ⊆ ⋃ n, t n) ∧
          (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
            (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · refine ⟨fun _ => ∅, fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
  obtain ⟨T, T_count, hT⟩ :
    ∃ T : Set s,
      T.Countable ∧ ⋃ x ∈ T, ball (f' (x : E)) (r (f' x)) = ⋃ x : s, ball (f' x) (r (f' x)) :=
    TopologicalSpace.isOpen_iUnion_countable _ fun x => isOpen_ball
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  let M : ℕ → T → Set E := fun n z =>
    {x | x ∈ s ∧ ∀ y ∈ s ∩ ball x (u n), ‖f y - f x - f' z (y - x)‖ ≤ r (f' z) * ‖y - x‖}
  have s_subset : ∀ x ∈ s, ∃ (n : ℕ) (z : T), x ∈ M n z := by
    intro x xs
    obtain ⟨z, zT, hz⟩ : ∃ z ∈ T, f' x ∈ ball (f' (z : E)) (r (f' z)) := by
      have : f' x ∈ ⋃ z ∈ T, ball (f' (z : E)) (r (f' z)) := by
        rw [hT]
        refine mem_iUnion.2 ⟨⟨x, xs⟩, ?_⟩
        simpa only [mem_ball, Subtype.coe_mk, dist_self] using (rpos (f' x)).bot_lt
      rwa [mem_iUnion₂, bex_def] at this
    obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ‖f' x - f' z‖ + ε ≤ r (f' z) := by
      refine ⟨r (f' z) - ‖f' x - f' z‖, ?_, le_of_eq (by abel)⟩
      simpa only [sub_pos] using mem_ball_iff_norm.mp hz
    obtain ⟨δ, δpos, hδ⟩ :
      ∃ (δ : ℝ), 0 < δ ∧ ball x δ ∩ s ⊆ {y | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
    obtain ⟨n, hn⟩ : ∃ n, u n < δ := ((tendsto_order.1 u_lim).2 _ δpos).exists
    refine ⟨n, ⟨z, zT⟩, ⟨xs, ?_⟩⟩
    intro y hy
    calc
      ‖f y - f x - (f' z) (y - x)‖ = ‖f y - f x - (f' x) (y - x) + (f' x - f' z) (y - x)‖ := by
        congr 1
        simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖f y - f x - (f' x) (y - x)‖ + ‖(f' x - f' z) (y - x)‖ := norm_add_le _ _
      _ ≤ ε * ‖y - x‖ + ‖f' x - f' z‖ * ‖y - x‖ := by
        refine add_le_add (hδ ?_) (ContinuousLinearMap.le_opNorm _ _)
        rw [inter_comm]
        exact inter_subset_inter_right _ (ball_subset_ball hn.le) hy
      _ ≤ r (f' z) * ‖y - x‖ := by
        rw [← add_mul, add_comm]
        gcongr
  have closure_M_subset : ∀ n z, s ∩ closure (M n z) ⊆ M n z := by
    rintro n z x ⟨xs, hx⟩
    refine ⟨xs, fun y hy => ?_⟩
    obtain ⟨a, aM, a_lim⟩ : ∃ a : ℕ → E, (∀ k, a k ∈ M n z) ∧ Tendsto a atTop (𝓝 x) :=
      mem_closure_iff_seq_limit.1 hx
    have L1 :
      Tendsto (fun k : ℕ => ‖f y - f (a k) - (f' z) (y - a k)‖) atTop
        (𝓝 ‖f y - f x - (f' z) (y - x)‖) := by
      apply Tendsto.norm
      have L : Tendsto (fun k => f (a k)) atTop (𝓝 (f x)) := by
        apply (hf' x xs).continuousWithinAt.tendsto.comp
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ a_lim
        exact Eventually.of_forall fun k => (aM k).1
      apply Tendsto.sub (tendsto_const_nhds.sub L)
      exact ((f' z).continuous.tendsto _).comp (tendsto_const_nhds.sub a_lim)
    have L2 : Tendsto (fun k : ℕ => (r (f' z) : ℝ) * ‖y - a k‖) atTop (𝓝 (r (f' z) * ‖y - x‖)) :=
      (tendsto_const_nhds.sub a_lim).norm.const_mul _
    have I : ∀ᶠ k in atTop, ‖f y - f (a k) - (f' z) (y - a k)‖ ≤ r (f' z) * ‖y - a k‖ := by
      have L : Tendsto (fun k => dist y (a k)) atTop (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist a_lim
      filter_upwards [(tendsto_order.1 L).2 _ hy.2]
      intro k hk
      exact (aM k).2 y ⟨hy.1, hk⟩
    exact le_of_tendsto_of_tendsto L1 L2 I
  rcases TopologicalSpace.exists_dense_seq E with ⟨d, hd⟩
  let K : ℕ → T → ℕ → Set E := fun n z p => closure (M n z) ∩ closedBall (d p) (u n / 3)
  have K_approx : ∀ (n) (z : T) (p), ApproximatesLinearOn f (f' z) (s ∩ K n z p) (r (f' z)) := by
    intro n z p x hx y hy
    have yM : y ∈ M n z := closure_M_subset _ _ ⟨hy.1, hy.2.1⟩
    refine yM.2 _ ⟨hx.1, ?_⟩
    calc
      dist x y ≤ dist x (d p) + dist y (d p) := dist_triangle_right _ _ _
      _ ≤ u n / 3 + u n / 3 := add_le_add hx.2.2 hy.2.2
      _ < u n := by linarith [u_pos n]
  have K_closed : ∀ (n) (z : T) (p), IsClosed (K n z p) := fun n z p =>
    isClosed_closure.inter isClosed_ball
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ × T × ℕ, Function.Surjective F := by
    haveI : Encodable T := T_count.toEncodable
    have : Nonempty T := by
      rcases hs with ⟨x, xs⟩
      rcases s_subset x xs with ⟨n, z, _⟩
      exact ⟨z⟩
    inhabit ↥T
    exact ⟨_, Encodable.surjective_decode_iget (ℕ × T × ℕ)⟩
  refine
    ⟨fun q => K (F q).1 (F q).2.1 (F q).2.2, fun q => f' (F q).2.1, fun n => K_closed _ _ _,
      fun x xs => ?_, fun q => K_approx _ _ _, fun _ q => ⟨(F q).2.1, (F q).2.1.1.2, rfl⟩⟩
  obtain ⟨n, z, hnz⟩ : ∃ (n : ℕ) (z : T), x ∈ M n z := s_subset x xs
  obtain ⟨p, hp⟩ : ∃ p : ℕ, x ∈ closedBall (d p) (u n / 3) := by
    have : Set.Nonempty (ball x (u n / 3)) := by simp only [nonempty_ball]; linarith [u_pos n]
    obtain ⟨p, hp⟩ : ∃ p : ℕ, d p ∈ ball x (u n / 3) := hd.exists_mem_open isOpen_ball this
    exact ⟨p, (mem_ball'.1 hp).le⟩
  obtain ⟨q, hq⟩ : ∃ q, F q = (n, z, p) := hF _
  apply mem_iUnion.2 ⟨q, _⟩
  simp (config := { zeta := false }) only [K, hq, mem_inter_iff, hp, and_true]
  exact subset_closure hnz
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt [SecondCountableTopology F]
    (f : E → F) (s : Set E) (f' : E → E →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (r : (E →L[ℝ] F) → ℝ≥0) (rpos : ∀ A, r A ≠ 0) :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] F),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n, t n) ∧
            (∀ n, ApproximatesLinearOn f (A n) (s ∩ t n) (r (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) := by
  rcases exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' r rpos with
    ⟨t, A, t_closed, st, t_approx, ht⟩
  refine
    ⟨disjointed t, A, disjoint_disjointed _,
      MeasurableSet.disjointed fun n => (t_closed n).measurableSet, ?_, ?_, ht⟩
  · rw [iUnion_disjointed]; exact st
  · intro n; exact (t_approx n).mono_set (inter_subset_inter_right _ (disjointed_subset _ _))
namespace MeasureTheory
theorem addHaar_image_le_mul_of_det_lt (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : ENNReal.ofReal |A.det| < m) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → μ (f '' s) ≤ m * μ s := by
  apply nhdsWithin_le_nhds
  let d := ENNReal.ofReal |A.det|
  obtain ⟨ε, hε, εpos⟩ :
    ∃ ε : ℝ, μ (closedBall 0 ε + A '' closedBall 0 1) < m * μ (closedBall 0 1) ∧ 0 < ε := by
    have HC : IsCompact (A '' closedBall 0 1) :=
      (ProperSpace.isCompact_closedBall _ _).image A.continuous
    have L0 :
      Tendsto (fun ε => μ (cthickening ε (A '' closedBall 0 1))) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact tendsto_measure_cthickening_of_isCompact HC
    have L1 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (μ (A '' closedBall 0 1))) := by
      apply L0.congr' _
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [← HC.add_closedBall_zero (le_of_lt hr), add_comm]
    have L2 :
      Tendsto (fun ε => μ (closedBall 0 ε + A '' closedBall 0 1)) (𝓝[>] 0)
        (𝓝 (d * μ (closedBall 0 1))) := by
      convert L1
      exact (addHaar_image_continuousLinearMap _ _ _).symm
    have I : d * μ (closedBall 0 1) < m * μ (closedBall 0 1) :=
      (ENNReal.mul_lt_mul_right (measure_closedBall_pos μ _ zero_lt_one).ne'
            measure_closedBall_lt_top.ne).2
        hm
    have H :
      ∀ᶠ b : ℝ in 𝓝[>] 0, μ (closedBall 0 b + A '' closedBall 0 1) < m * μ (closedBall 0 1) :=
      (tendsto_order.1 L2).2 _ I
    exact (H.and self_mem_nhdsWithin).exists
  have : Iio (⟨ε, εpos.le⟩ : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0) := by apply Iio_mem_nhds; exact εpos
  filter_upwards [this]
  intro δ hδ s f hf
  simp only [mem_Iio, ← NNReal.coe_lt_coe, NNReal.coe_mk] at hδ
  have I : ∀ x r, x ∈ s → 0 ≤ r → μ (f '' (s ∩ closedBall x r)) ≤ m * μ (closedBall x r) := by
    intro x r xs r0
    have K : f '' (s ∩ closedBall x r) ⊆ A '' closedBall 0 r + closedBall (f x) (ε * r) := by
      rintro y ⟨z, ⟨zs, zr⟩, rfl⟩
      rw [mem_closedBall_iff_norm] at zr
      apply Set.mem_add.2 ⟨A (z - x), _, f z - f x - A (z - x) + f x, _, _⟩
      · apply mem_image_of_mem
        simpa only [dist_eq_norm, mem_closedBall, mem_closedBall_zero_iff, sub_zero] using zr
      · rw [mem_closedBall_iff_norm, add_sub_cancel_right]
        calc
          ‖f z - f x - A (z - x)‖ ≤ δ * ‖z - x‖ := hf _ zs _ xs
          _ ≤ ε * r := by gcongr
      · simp only [map_sub, Pi.sub_apply]
        abel
    have :
      A '' closedBall 0 r + closedBall (f x) (ε * r) =
        {f x} + r • (A '' closedBall 0 1 + closedBall 0 ε) := by
      rw [smul_add, ← add_assoc, add_comm {f x}, add_assoc, smul_closedBall _ _ εpos.le, smul_zero,
        singleton_add_closedBall_zero, ← image_smul_set ℝ E E A,
        _root_.smul_closedBall _ _ zero_le_one, smul_zero, Real.norm_eq_abs, abs_of_nonneg r0,
        mul_one, mul_comm]
    rw [this] at K
    calc
      μ (f '' (s ∩ closedBall x r)) ≤ μ ({f x} + r • (A '' closedBall 0 1 + closedBall 0 ε)) :=
        measure_mono K
      _ = ENNReal.ofReal (r ^ finrank ℝ E) * μ (A '' closedBall 0 1 + closedBall 0 ε) := by
        simp only [abs_of_nonneg r0, addHaar_smul, image_add_left, abs_pow, singleton_add,
          measure_preimage_add]
      _ ≤ ENNReal.ofReal (r ^ finrank ℝ E) * (m * μ (closedBall 0 1)) := by
        rw [add_comm]; gcongr
      _ = m * μ (closedBall x r) := by simp only [addHaar_closedBall' μ _ r0]; ring
  have J : ∀ᶠ a in 𝓝[>] (0 : ℝ≥0∞), μ (f '' s) ≤ m * (μ s + a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [mem_Ioi] at ha
    obtain ⟨t, r, t_count, ts, rpos, st, μt⟩ :
      ∃ (t : Set E) (r : E → ℝ),
        t.Countable ∧
          t ⊆ s ∧
            (∀ x : E, x ∈ t → 0 < r x) ∧
              (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧
                (∑' x : ↥t, μ (closedBall (↑x) (r ↑x))) ≤ μ s + a :=
      Besicovitch.exists_closedBall_covering_tsum_measure_le μ ha.ne' (fun _ => Ioi 0) s
        fun x _ δ δpos => ⟨δ / 2, by simp [half_pos δpos, δpos]⟩
    haveI : Encodable t := t_count.toEncodable
    calc
      μ (f '' s) ≤ μ (⋃ x : t, f '' (s ∩ closedBall x (r x))) := by
        rw [biUnion_eq_iUnion] at st
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact image_subset _ (subset_inter (Subset.refl _) st)
      _ ≤ ∑' x : t, μ (f '' (s ∩ closedBall x (r x))) := measure_iUnion_le _
      _ ≤ ∑' x : t, m * μ (closedBall x (r x)) :=
        (ENNReal.tsum_le_tsum fun x => I x (r x) (ts x.2) (rpos x x.2).le)
      _ ≤ m * (μ s + a) := by rw [ENNReal.tsum_mul_left]; gcongr
  have L : Tendsto (fun a => (m : ℝ≥0∞) * (μ s + a)) (𝓝[>] 0) (𝓝 (m * (μ s + 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ENNReal.Tendsto.const_mul (tendsto_const_nhds.add tendsto_id)
    simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
  rw [add_zero] at L
  exact ge_of_tendsto L J
theorem mul_le_addHaar_image_of_lt_det (A : E →L[ℝ] E) {m : ℝ≥0}
    (hm : (m : ℝ≥0∞) < ENNReal.ofReal |A.det|) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      ∀ (s : Set E) (f : E → E), ApproximatesLinearOn f A s δ → (m : ℝ≥0∞) * μ s ≤ μ (f '' s) := by
  apply nhdsWithin_le_nhds
  rcases eq_or_lt_of_le (zero_le m) with (rfl | mpos)
  · filter_upwards
    simp only [forall_const, zero_mul, imp_true_iff, zero_le, ENNReal.coe_zero]
  have hA : A.det ≠ 0 := by
    intro h; simp only [h, ENNReal.not_lt_zero, ENNReal.ofReal_zero, abs_zero] at hm
  let B := A.toContinuousLinearEquivOfDetNeZero hA
  have I : ENNReal.ofReal |(B.symm : E →L[ℝ] E).det| < (m⁻¹ : ℝ≥0) := by
    simp only [ENNReal.ofReal, abs_inv, Real.toNNReal_inv, ContinuousLinearEquiv.det_coe_symm,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, ENNReal.coe_lt_coe] at hm ⊢
    exact NNReal.inv_lt_inv mpos.ne' hm
  obtain ⟨δ₀, δ₀pos, hδ₀⟩ :
    ∃ δ : ℝ≥0,
      0 < δ ∧
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t := by
    have :
      ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0,
        ∀ (t : Set E) (g : E → E),
          ApproximatesLinearOn g (B.symm : E →L[ℝ] E) t δ → μ (g '' t) ≤ ↑m⁻¹ * μ t :=
      addHaar_image_le_mul_of_det_lt μ B.symm I
    rcases (this.and self_mem_nhdsWithin).exists with ⟨δ₀, h, h'⟩
    exact ⟨δ₀, h', h⟩
  have L1 : ∀ᶠ δ in 𝓝 (0 : ℝ≥0), Subsingleton E ∨ δ < ‖(B.symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases h : Subsingleton E
    · simp only [h, true_or, eventually_const]
    simp only [h, false_or]
    apply Iio_mem_nhds
    simpa only [h, false_or, inv_pos] using B.subsingleton_or_nnnorm_symm_pos
  have L2 :
    ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ < δ₀ := by
    have :
      Tendsto (fun δ => ‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - δ)⁻¹ * δ) (𝓝 0)
        (𝓝 (‖(B.symm : E →L[ℝ] E)‖₊ * (‖(B.symm : E →L[ℝ] E)‖₊⁻¹ - 0)⁻¹ * 0)) := by
      rcases eq_or_ne ‖(B.symm : E →L[ℝ] E)‖₊ 0 with (H | H)
      · simpa only [H, zero_mul] using tendsto_const_nhds
      refine Tendsto.mul (tendsto_const_nhds.mul ?_) tendsto_id
      refine (Tendsto.sub tendsto_const_nhds tendsto_id).inv₀ ?_
      simpa only [tsub_zero, inv_eq_zero, Ne] using H
    simp only [mul_zero] at this
    exact (tendsto_order.1 this).2 δ₀ δ₀pos
  filter_upwards [L1, L2]
  intro δ h1δ h2δ s f hf
  have hf' : ApproximatesLinearOn f (B : E →L[ℝ] E) s δ := by convert hf
  let F := hf'.toPartialEquiv h1δ
  suffices H : μ (F.symm '' F.target) ≤ (m⁻¹ : ℝ≥0) * μ F.target by
    change (m : ℝ≥0∞) * μ F.source ≤ μ F.target
    rwa [← F.symm_image_target_eq_source, mul_comm, ← ENNReal.le_div_iff_mul_le, div_eq_mul_inv,
      mul_comm, ← ENNReal.coe_inv mpos.ne']
    · apply Or.inl
      simpa only [ENNReal.coe_eq_zero, Ne] using mpos.ne'
    · simp only [ENNReal.coe_ne_top, true_or, Ne, not_false_iff]
  exact hδ₀ _ _ ((hf'.to_inv h1δ).mono_num h2δ.le)
theorem _root_.ApproximatesLinearOn.norm_fderiv_sub_le {A : E →L[ℝ] E} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s) (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : ∀ᵐ x ∂μ.restrict s, ‖f' x - A‖₊ ≤ δ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s, ae_restrict_mem hs]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    ∃ r : ℝ,
      (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [_root_.add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := add_le_add_left (mem_closedBall_iff_norm.1 az) _
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [ContinuousLinearMap.map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        congr 1
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, ContinuousLinearMap.coe_sub',
          eq_self_iff_true, sub_left_inj, Pi.sub_apply, ContinuousLinearMap.map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_left rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr
theorem addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : DifferentiableOn ℝ f s)
    (hs : μ s = 0) : μ (f '' s) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + 1 : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + 1
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, zero_lt_one, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, _, _, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = fderivWithin ℝ f s y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderivWithin ℝ f s)
      (fun x xs => (hf x xs).hasFDerivWithinAt) δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_subset f (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + 1 : ℝ≥0) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2
      exact ht n
    _ ≤ ∑' n, ((Real.toNNReal |(A n).det| + 1 : ℝ≥0) : ℝ≥0∞) * 0 := by
      refine ENNReal.tsum_le_tsum fun n => mul_le_mul_left' ?_ _
      exact le_trans (measure_mono inter_subset_left) (le_of_eq hs)
    _ = 0 := by simp only [tsum_zero, mul_zero]
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (R : ℝ) (hs : s ⊆ closedBall 0 R) (ε : ℝ≥0)
    (εpos : 0 < ε) (h'f' : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) ≤ ε * μ (closedBall 0 R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's); · simp only [measure_empty, zero_le, image_empty]
  have :
      ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ (t : Set E), ApproximatesLinearOn f A t δ →
          μ (f '' t) ≤ (Real.toNNReal |A.det| + ε : ℝ≥0) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, h'⟩
    exact ⟨δ, h', fun t ht => h t f ht⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (Real.toNNReal |(A n).det| + ε : ℝ≥0) * μ (s ∩ t n) := by
      gcongr
      exact (hδ (A _)).2 _ (ht _)
    _ = ∑' n, ε * μ (s ∩ t n) := by
      congr with n
      rcases Af' h's n with ⟨y, ys, hy⟩
      simp only [hy, h'f' y ys, Real.toNNReal_zero, abs_zero, zero_add]
    _ ≤ ε * ∑' n, μ (closedBall 0 R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * μ (⋃ n, closedBall 0 R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * μ (closedBall 0 R) := by
      rw [← inter_iUnion]
      exact mul_le_mul_left' (measure_mono inter_subset_left) _
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (h'f' : ∀ x ∈ s, (f' x).det = 0) :
    μ (f '' s) = 0 := by
  suffices H : ∀ R, μ (f '' (s ∩ closedBall 0 R)) = 0 by
    apply le_antisymm _ (zero_le _)
    rw [← iUnion_inter_closedBall_nat s 0]
    calc
      μ (f '' ⋃ n : ℕ, s ∩ closedBall 0 n) ≤ ∑' n : ℕ, μ (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
  intro R
  have A : ∀ (ε : ℝ≥0), 0 < ε → μ (f '' (s ∩ closedBall 0 R)) ≤ ε * μ (closedBall 0 R) :=
    fun ε εpos =>
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero_aux μ
      (fun x hx => (hf' x hx.1).mono inter_subset_left) R inter_subset_right ε εpos
      fun x hx => h'f' x hx.1
  have B : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝[>] 0) (𝓝 0) := by
    have :
      Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * μ (closedBall 0 R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * μ (closedBall 0 R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  apply le_antisymm _ (zero_le _)
  apply ge_of_tendsto B
  filter_upwards [self_mem_nhdsWithin]
  exact A
theorem aemeasurable_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : AEMeasurable f' (μ.restrict s) := by
  refine aemeasurable_of_unif_approx fun ε εpos => ?_
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  have δpos : 0 < δ := εpos
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, _⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) δ) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' (fun _ => δ) fun _ =>
      δpos.ne'
  obtain ⟨g, g_meas, hg⟩ :
      ∃ g : E → E →L[ℝ] E, Measurable g ∧ ∀ (n : ℕ) (x : E), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const) <|
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, g_meas.aemeasurable, ?_⟩
  suffices H : ∀ᵐ x : E ∂sum fun n ↦ μ.restrict (s ∩ t n), dist (g x) (f' x) ≤ ε by
    have : μ.restrict s ≤ sum fun n => μ.restrict (s ∩ t n) := by
      have : s = ⋃ n, s ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
      conv_lhs => rw [this]
      exact restrict_iUnion_le
    exact ae_mono this H
  refine ae_sum_iff.2 fun n => ?_
  have E₁ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), ‖f' x - A n‖₊ ≤ δ :=
    (ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
      (hf' x hx.1).mono inter_subset_left
  have E₂ : ∀ᵐ x : E ∂μ.restrict (s ∩ t n), g x = A n := by
    suffices H : ∀ᵐ x : E ∂μ.restrict (t n), g x = A n from
      ae_mono (restrict_mono inter_subset_right le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  filter_upwards [E₁, E₂] with x hx1 hx2
  rw [← nndist_eq_nnnorm] at hx1
  rw [hx2, dist_comm]
  exact hx1
theorem aemeasurable_ofReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => ENNReal.ofReal |(f' x).det|) (μ.restrict s) := by
  apply ENNReal.measurable_ofReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'
theorem aemeasurable_toNNReal_abs_det_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => |(f' x).det|.toNNReal) (μ.restrict s) := by
  apply measurable_real_toNNReal.comp_aemeasurable
  refine continuous_abs.measurable.comp_aemeasurable ?_
  refine ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable ?_
  exact aemeasurable_fderivWithin μ hs hf'
theorem measurable_image_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf
theorem measurableEmbedding_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    MeasurableEmbedding (s.restrict f) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  this.continuousOn.measurableEmbedding hs hf
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) {ε : ℝ≥0} (εpos : 0 < ε) :
    μ (f '' s) ≤ (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              μ (g '' t) ≤ (ENNReal.ofReal |A.det| + ε) * μ t := by
    intro A
    let m : ℝ≥0 := Real.toNNReal |A.det| + ε
    have I : ENNReal.ofReal |A.det| < m := by
      simp only [m, ENNReal.ofReal, lt_add_iff_pos_right, εpos, ENNReal.coe_lt_coe]
    rcases ((addHaar_image_le_mul_of_det_lt μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε :=
      continuousAt_iff.1 (ContinuousLinearMap.continuous_det (E := E)).continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      calc
        ‖B - A‖ ≤ (min δ δ'' : ℝ≥0) := hB
        _ ≤ δ'' := by simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
        _ < δ' := half_lt_self δ'pos
    · intro t g htg
      exact h t g (htg.mono_num (min_le_left _ _))
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  calc
    μ (f '' s) ≤ μ (⋃ n, f '' (s ∩ t n)) := by
      apply measure_mono
      rw [← image_iUnion, ← inter_iUnion]
      exact image_subset f (subset_inter Subset.rfl t_cover)
    _ ≤ ∑' n, μ (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ENNReal.ofReal |(A n).det| + ε) * μ (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply (hδ (A n)).2.2
      exact ht n
    _ = ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(A n).det| ≤ |(f' x).det| + ε :=
        calc
          |(A n).det| = |(f' x).det - ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(f' x).det| + |(f' x).det - (A n).det| := abs_sub _ _
          _ ≤ |(f' x).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(A n).det| + ε ≤ ENNReal.ofReal (|(f' x).det| + ε) + ε := by gcongr
        _ = ENNReal.ofReal |(f' x).det| + 2 * ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, two_mul, add_assoc, NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    _ = ∫⁻ x in ⋃ n, s ∩ t n, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      have M : ∀ n : ℕ, MeasurableSet (s ∩ t n) := fun n => hs.inter (t_meas n)
      rw [lintegral_iUnion M]
      exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| + 2 * ε ∂μ := by
      rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
    _ = (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s := by
      simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
theorem addHaar_image_le_lintegral_abs_det_fderiv_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  have :
    Tendsto (fun ε : ℝ≥0 => (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact addHaar_image_le_lintegral_abs_det_fderiv_aux1 μ hs hf' εpos
theorem addHaar_image_le_lintegral_abs_det_fderiv (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  let u n := disjointed (spanningSets μ) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μ (f '' s) ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      conv_lhs => rw [A, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        addHaar_image_le_lintegral_abs_det_fderiv_aux2 μ (hs.inter (u_meas n)) _ fun x hx =>
          (hf' x hx.1).mono inter_subset_left
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_rhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux1 (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) {ε : ℝ≥0} (εpos : 0 < ε) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) + 2 * ε * μ s := by
  have :
    ∀ A : E →L[ℝ] E,
      ∃ δ : ℝ≥0,
        0 < δ ∧
          (∀ B : E →L[ℝ] E, ‖B - A‖ ≤ δ → |B.det - A.det| ≤ ε) ∧
            ∀ (t : Set E) (g : E → E), ApproximatesLinearOn g A t δ →
              ENNReal.ofReal |A.det| * μ t ≤ μ (g '' t) + ε * μ t := by
    intro A
    obtain ⟨δ', δ'pos, hδ'⟩ : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ B, dist B A < δ' → dist B.det A.det < ↑ε :=
      continuousAt_iff.1 (ContinuousLinearMap.continuous_det (E := E)).continuousAt ε εpos
    let δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩
    have I'' : ∀ B : E →L[ℝ] E, ‖B - A‖ ≤ ↑δ'' → |B.det - A.det| ≤ ↑ε := by
      intro B hB
      rw [← Real.dist_eq]
      apply (hδ' B _).le
      rw [dist_eq_norm]
      exact hB.trans_lt (half_lt_self δ'pos)
    rcases eq_or_ne A.det 0 with (hA | hA)
    · refine ⟨δ'', half_pos δ'pos, I'', ?_⟩
      simp only [hA, forall_const, zero_mul, ENNReal.ofReal_zero, imp_true_iff,
        zero_le, abs_zero]
    let m : ℝ≥0 := Real.toNNReal |A.det| - ε
    have I : (m : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
      simp only [m, ENNReal.ofReal, ENNReal.coe_sub]
      apply ENNReal.sub_lt_self ENNReal.coe_ne_top
      · simpa only [abs_nonpos_iff, Real.toNNReal_eq_zero, ENNReal.coe_eq_zero, Ne] using hA
      · simp only [εpos.ne', ENNReal.coe_eq_zero, Ne, not_false_iff]
    rcases ((mul_le_addHaar_image_of_lt_det μ A I).and self_mem_nhdsWithin).exists with ⟨δ, h, δpos⟩
    refine ⟨min δ δ'', lt_min δpos (half_pos δ'pos), ?_, ?_⟩
    · intro B hB
      apply I'' _ (hB.trans _)
      simp only [le_refl, NNReal.coe_min, min_le_iff, or_true]
    · intro t g htg
      rcases eq_or_ne (μ t) ∞ with (ht | ht)
      · simp only [ht, εpos.ne', ENNReal.mul_top, ENNReal.coe_eq_zero, le_top, Ne,
          not_false_iff, _root_.add_top]
      have := h t g (htg.mono_num (min_le_left _ _))
      rwa [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at this
      simp only [ht, imp_true_iff, Ne, not_false_iff]
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set E) (A : ℕ → E →L[ℝ] E),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (s ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn f (A n) (s ∩ t n) (δ (A n))) ∧
              (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ fun A => (hδ A).1.ne'
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n => hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
    _ ≤ ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal |(A n).det| + ε ∂μ := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply lintegral_mono_ae
      filter_upwards [(ht n).norm_fderiv_sub_le μ (hs.inter (t_meas n)) f' fun x hx =>
          (hf' x hx.1).mono inter_subset_left]
      intro x hx
      have I : |(f' x).det| ≤ |(A n).det| + ε :=
        calc
          |(f' x).det| = |(A n).det + ((f' x).det - (A n).det)| := by congr 1; abel
          _ ≤ |(A n).det| + |(f' x).det - (A n).det| := abs_add _ _
          _ ≤ |(A n).det| + ε := add_le_add le_rfl ((hδ (A n)).2.1 _ hx)
      calc
        ENNReal.ofReal |(f' x).det| ≤ ENNReal.ofReal (|(A n).det| + ε) :=
          ENNReal.ofReal_le_ofReal I
        _ = ENNReal.ofReal |(A n).det| + ε := by
          simp only [ENNReal.ofReal_add, abs_nonneg, NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    _ = ∑' n, (ENNReal.ofReal |(A n).det| * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
    _ ≤ ∑' n, (μ (f '' (s ∩ t n)) + ε * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
      gcongr
      exact (hδ (A _)).2.2 _ _ (ht _)
    _ = μ (f '' s) + 2 * ε * μ s := by
      conv_rhs => rw [s_eq]
      rw [image_iUnion, measure_iUnion]; rotate_left
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (t_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)
      rw [measure_iUnion]; rotate_left
      · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right
      · exact fun i => hs.inter (t_meas i)
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      congr 1
      ext1 i
      rw [mul_assoc, two_mul, add_assoc]
theorem lintegral_abs_det_fderiv_le_addHaar_image_aux2 (hs : MeasurableSet s) (h's : μ s ≠ ∞)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  have :
    Tendsto (fun ε : ℝ≥0 => μ (f '' s) + 2 * ε * μ s) (𝓝[>] 0)
      (𝓝 (μ (f '' s) + 2 * (0 : ℝ≥0) * μ s)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h's)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at this
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin]
  intro ε εpos
  rw [mem_Ioi] at εpos
  exact lintegral_abs_det_fderiv_le_addHaar_image_aux1 μ hs hf' hf εpos
theorem lintegral_abs_det_fderiv_le_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) ≤ μ (f '' s) := by
  let u n := disjointed (spanningSets μ) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) =
        ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal |(f' x).det| ∂μ := by
      conv_lhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right
    _ ≤ ∑' n, μ (f '' (s ∩ u n)) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply
        lintegral_abs_det_fderiv_le_addHaar_image_aux2 μ (hs.inter (u_meas n)) _
          (fun x hx => (hf' x hx.1).mono inter_subset_left) (hf.mono inter_subset_left)
      have : μ (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top μ n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = μ (f '' s) := by
      conv_rhs => rw [A, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact
          Disjoint.mono inter_subset_right inter_subset_right
            (disjoint_disjointed _ hij)
      · intro i
        exact
          measurable_image_of_fderivWithin (hs.inter (u_meas i))
            (fun x hx => (hf' x hx.1).mono inter_subset_left)
            (hf.mono inter_subset_left)
theorem lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) :=
  le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')
theorem map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (h'f : Measurable f) :
    Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) =
      μ.restrict (f '' s) := by
  apply Measure.ext fun t ht => ?_
  rw [map_apply h'f ht, withDensity_apply _ (h'f ht), Measure.restrict_apply ht,
    restrict_restrict (h'f ht),
    lintegral_abs_det_fderiv_eq_addHaar_image μ ((h'f ht).inter hs)
      (fun x hx => (hf' x hx.2).mono inter_subset_right) (hf.mono inter_subset_right),
    image_preimage_inter]
theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map (s.restrict f) (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (f '' s) := by
  obtain ⟨u, u_meas, uf⟩ : ∃ u, Measurable u ∧ EqOn u f s := by
    classical
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    have : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
    exact this.continuousOn
  have u' : ∀ x ∈ s, HasFDerivWithinAt u (f' x) s x := fun x hx =>
    (hf' x hx).congr (fun y hy => uf hy) (uf hx)
  set F : s → E := u ∘ (↑) with hF
  have A :
    Measure.map F (comap (↑) (μ.withDensity fun x => ENNReal.ofReal |(f' x).det|)) =
      μ.restrict (u '' s) := by
    rw [hF, ← Measure.map_map u_meas measurable_subtype_coe, map_comap_subtype_coe hs,
      restrict_withDensity hs]
    exact map_withDensity_abs_det_fderiv_eq_addHaar μ hs u' (hf.congr uf.symm) u_meas
  rw [uf.image_eq] at A
  have : F = s.restrict f := by
    ext x
    exact uf x.2
  rwa [this] at A
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).lintegral_map]
  simp only [Set.restrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · simp only [Pi.mul_apply]
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact aemeasurable_ofReal_abs_det_fderivWithin μ hs hf'
theorem integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (f x)) s μ := by
  rw [IntegrableOn, ← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integrable_map_iff]
  simp only [Set.restrict_eq, ← Function.comp_assoc, ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff, map_comap_subtype_coe hs,
    restrict_withDensity hs, integrable_withDensity_iff_integrable_coe_smul₀]
  · simp_rw [IntegrableOn, Real.coe_toNNReal _ (abs_nonneg _), Function.comp_apply]
  · exact aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf'
theorem integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.restrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    setIntegral_withDensity_eq_setIntegral_smul₀
      (aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf') _ hs]
  congr with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (abs_nonneg (f' x).det)]
theorem det_one_smulRight {𝕜 : Type*} [NormedField 𝕜] (v : 𝕜) :
    ((1 : 𝕜 →L[𝕜] 𝕜).smulRight v).det = v := by
  have : (1 : 𝕜 →L[𝕜] 𝕜).smulRight v = v • (1 : 𝕜 →L[𝕜] 𝕜) := by
    ext1
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply, mul_one]
  rw [this, ContinuousLinearMap.det, ContinuousLinearMap.coe_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.det_smul,
    Module.finrank_self, LinearMap.det_id, pow_one, mul_one]
theorem integrableOn_image_iff_integrableOn_abs_deriv_smul {s : Set ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s := by
  simpa only [det_one_smulRight] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
theorem integral_image_eq_integral_abs_deriv_smul {s : Set ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → F) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  simpa only [det_one_smulRight] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g
theorem integral_target_eq_integral_abs_det_fderiv_smul {f : PartialHomeomorph E E}
    (hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x) (g : E → F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ := by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt
section withDensity
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (hf : MeasurableEmbedding f)
    {g : E → ℝ} (hg : ∀ᵐ x ∂μ, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [Measure.comap_apply f hf.injective (fun t ht ↦ hf.measurableSet_image' ht) _ hs,
    withDensity_apply _ (hf.measurableSet_image' hs),
    ← ofReal_integral_eq_lintegral_ofReal hg_int
      ((ae_restrict_iff' (hf.measurableSet_image' hs)).mpr hg),
    integral_image_eq_integral_abs_det_fderiv_smul μ hs hf' hf.injective.injOn]
  simp_rw [smul_eq_mul]
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    (hs : MeasurableSet s) (f : E ≃ᵐ E)
    {g : E → ℝ} (hg : ∀ᵐ x ∂μ, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s) μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |(f' x).det| * g (f x) ∂μ) := by
  rw [MeasurableEquiv.map_symm,
    MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul μ hs
      f.measurableEmbedding hg hg_int hf']
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [hf.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul volume hs
    hg hg_int hf']
  simp only [det_one_smulRight]
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hg_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f hg hg_int hf']
  simp only [det_one_smulRight]
lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul'
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) :=
  hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul hs
    (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
    (fun x _ => (hf' x).hasDerivWithinAt)
lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
      (fun x _ => (hf' x).hasDerivWithinAt)]
  simp only [det_one_smulRight]
end withDensity
end MeasureTheory