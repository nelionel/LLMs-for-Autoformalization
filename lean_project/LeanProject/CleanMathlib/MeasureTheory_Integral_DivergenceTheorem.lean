import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral
open Set Finset TopologicalSpace Function BoxIntegral MeasureTheory Filter
open scoped Classical Topology Interval
universe u
namespace MeasureTheory
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
section
variable {n : ℕ}
local macro:arg t:term:max noWs "ⁿ" : term => `(Fin n → $t)
local macro:arg t:term:max noWs "ⁿ⁺¹" : term => `(Fin (n + 1) → $t)
local notation "e " i => Pi.single i 1
section
theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : ∀ x ∈ (Box.Icc I) \ s, HasFDerivWithinAt f (f' x) (Box.Icc I) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  simp only [← setIntegral_congr_set (Box.coe_ae_eq_Icc _)]
  have A := (Hi.mono_set Box.coe_subset_Icc).hasBoxIntegral ⊥ rfl
  have B :=
    hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I f f' (s ∩ Box.Icc I)
      (hs.mono inter_subset_left) (fun x hx => Hc _ hx.2) fun x hx =>
      Hd _ ⟨hx.1, fun h => hx.2 ⟨h, hx.1⟩⟩
  rw [continuousOn_pi] at Hc
  refine (A.unique B).trans (sum_congr rfl fun i _ => ?_)
  refine congr_arg₂ Sub.sub ?_ ?_
  · have := Box.continuousOn_face_Icc (Hc i) (Set.right_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq
  · have := Box.continuousOn_face_Icc (Hc i) (Set.left_mem_Icc.2 (I.lower_le_upper i))
    have := (this.integrableOn_compact (μ := volume) (Box.isCompact_Icc _)).mono_set
      Box.coe_subset_Icc
    exact (this.hasBoxIntegral ⊥ rfl).integral_eq
theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₂ (I : Box (Fin (n + 1)))
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹)
    (s : Set ℝⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Box.Icc I))
    (Hd : ∀ x ∈ Box.Ioo I \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (∑ i, f' · (e i) i) (Box.Icc I)) :
    (∫ x in Box.Icc I, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in Box.Icc (I.face i), f (i.insertNth (I.upper i) x) i) -
          ∫ x in Box.Icc (I.face i), f (i.insertNth (I.lower i) x) i) := by
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩
  have hJ_sub' : ∀ k, Box.Icc (J k) ⊆ Box.Icc I := fun k => (hJ_sub k).trans I.Ioo_subset_Icc
  have hJ_le : ∀ k, J k ≤ I := fun k => Box.le_iff_Icc.2 (hJ_sub' k)
  have HcJ : ∀ k, ContinuousOn f (Box.Icc (J k)) := fun k => Hc.mono (hJ_sub' k)
  have HdJ : ∀ (k), ∀ x ∈ (Box.Icc (J k)) \ s, HasFDerivWithinAt f (f' x) (Box.Icc (J k)) x :=
    fun k x hx => (Hd x ⟨hJ_sub k hx.1, hx.2⟩).hasFDerivWithinAt
  have HiJ : ∀ k, IntegrableOn (∑ i, f' · (e i) i) (Box.Icc (J k)) volume := fun k =>
    Hi.mono_set (hJ_sub' k)
  have HJ_eq := fun k =>
    integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (J k) f f' s hs (HcJ k) (HdJ k)
      (HiJ k)
  have hI_tendsto :
    Tendsto (fun k => ∫ x in Box.Icc (J k), ∑ i, f' x (e i) i) atTop
      (𝓝 (∫ x in Box.Icc I, ∑ i, f' x (e i) i)) := by
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _)] at Hi ⊢
    rw [← Box.iUnion_Ioo_of_tendsto J.monotone hJl hJu] at Hi ⊢
    exact tendsto_setIntegral_of_monotone (fun k => (J k).measurableSet_Ioo)
      (Box.Ioo.comp J).monotone Hi
  refine tendsto_nhds_unique_of_eventuallyEq hI_tendsto ?_ (Eventually.of_forall HJ_eq)
  clear hI_tendsto
  rw [tendsto_pi_nhds] at hJl hJu
  suffices ∀ (i : Fin (n + 1)) (c : ℕ → ℝ) (d), (∀ k, c k ∈ Icc (I.lower i) (I.upper i)) →
    Tendsto c atTop (𝓝 d) →
      Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth (c k) x) i) atTop
        (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) by
    rw [Box.Icc_eq_pi] at hJ_sub'
    refine tendsto_finset_sum _ fun i _ => (this _ _ _ ?_ (hJu _)).sub (this _ _ _ ?_ (hJl _))
    exacts [fun k => hJ_sub' k (J k).upper_mem_Icc _ trivial, fun k =>
      hJ_sub' k (J k).lower_mem_Icc _ trivial]
  intro i c d hc hcd
  have hd : d ∈ Icc (I.lower i) (I.upper i) :=
    isClosed_Icc.mem_of_tendsto hcd (Eventually.of_forall hc)
  have Hic : ∀ k, IntegrableOn (fun x => f (i.insertNth (c k) x) i) (Box.Icc (I.face i)) := fun k =>
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) (hc k)).integrableOn_Icc
  have Hid : IntegrableOn (fun x => f (i.insertNth d x) i) (Box.Icc (I.face i)) :=
    (Box.continuousOn_face_Icc ((continuous_apply i).comp_continuousOn Hc) hd).integrableOn_Icc
  have H :
    Tendsto (fun k => ∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i) atTop
      (𝓝 <| ∫ x in Box.Icc (I.face i), f (i.insertNth d x) i) := by
    have hIoo : (⋃ k, Box.Ioo ((J k).face i)) = Box.Ioo (I.face i) :=
      Box.iUnion_Ioo_of_tendsto ((Box.monotone_face i).comp J.monotone)
        (tendsto_pi_nhds.2 fun _ => hJl _) (tendsto_pi_nhds.2 fun _ => hJu _)
    simp only [IntegrableOn, ← Measure.restrict_congr_set (Box.Ioo_ae_eq_Icc _), ← hIoo] at Hid ⊢
    exact tendsto_setIntegral_of_monotone (fun k => ((J k).face i).measurableSet_Ioo)
      (Box.Ioo.monotone.comp ((Box.monotone_face i).comp J.monotone)) Hid
  refine H.congr_dist (Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε εpos => ?_)
  have hvol_pos : ∀ J : Box (Fin n), 0 < ∏ j, (J.upper j - J.lower j) := fun J =>
    prod_pos fun j hj => sub_pos.2 <| J.lower_lt_upper _
  rcases Metric.uniformContinuousOn_iff_le.1 (I.isCompact_Icc.uniformContinuousOn_of_continuous Hc)
      (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) (div_pos εpos (hvol_pos (I.face i)))
    with ⟨δ, δpos, hδ⟩
  refine (hcd.eventually (Metric.ball_mem_nhds _ δpos)).mono fun k hk => ?_
  have Hsub : Box.Icc ((J k).face i) ⊆ Box.Icc (I.face i) :=
    Box.le_iff_Icc.1 (Box.face_mono (hJ_le _) i)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm,
    ← integral_sub (Hid.mono_set Hsub) ((Hic _).mono_set Hsub)]
  calc
    ‖∫ x in Box.Icc ((J k).face i), f (i.insertNth d x) i - f (i.insertNth (c k) x) i‖ ≤
        (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) *
          (volume (Box.Icc ((J k).face i))).toReal := by
      refine norm_setIntegral_le_of_norm_le_const' (((J k).face i).measure_Icc_lt_top _)
        ((J k).face i).measurableSet_Icc fun x hx => ?_
      rw [← dist_eq_norm]
      calc
        dist (f (i.insertNth d x) i) (f (i.insertNth (c k) x) i) ≤
            dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) :=
          dist_le_pi_dist (f (i.insertNth d x)) (f (i.insertNth (c k) x)) i
        _ ≤ ε / ∏ j, ((I.face i).upper j - (I.face i).lower j) :=
          hδ _ (I.mapsTo_insertNth_face_Icc hd <| Hsub hx) _
            (I.mapsTo_insertNth_face_Icc (hc _) <| Hsub hx) ?_
      rw [Fin.dist_insertNth_insertNth, dist_self, dist_comm]
      exact max_le hk.le δpos.lt.le
    _ ≤ ε := by
      rw [Box.Icc_def, Real.volume_Icc_pi_toReal ((J k).face i).lower_le_upper,
        ← le_div_iff₀ (hvol_pos _)]
      gcongr
      exacts [hvol_pos _, fun _ _ ↦ sub_nonneg.2 (Box.lower_le_upper _ _),
        (hJ_sub' _ (J _).upper_mem_Icc).2 _, (hJ_sub' _ (J _).lower_mem_Icc).1 _]
variable (a b : Fin (n + 1) → ℝ)
local notation "face " i => Set.Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i)
local notation:max "frontFace " i:arg => Fin.insertNth i (b i)
local notation:max "backFace " i:arg => Fin.insertNth i (a i)
theorem integral_divergence_of_hasFDerivWithinAt_off_countable (hle : a ≤ b)
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
    (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹)
    (s : Set ℝⁿ⁺¹) (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' x (e i) i) =
      ∑ i : Fin (n + 1),
        ((∫ x in face i, f (frontFace i x) i) - ∫ x in face i, f (backFace i x) i) := by
  rcases em (∃ i, a i = b i) with (⟨i, hi⟩ | hne)
  · 
    rw [volume_pi, ← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt
    have : (pi Set.univ fun j => Ioc (a j) (b j)) = ∅ := univ_pi_eq_empty hi'
    rw [this, setIntegral_empty, sum_eq_zero]
    rintro j -
    rcases eq_or_ne i j with (rfl | hne)
    · simp [hi]
    · rcases Fin.exists_succAbove_eq hne with ⟨i, rfl⟩
      have : Icc (a ∘ j.succAbove) (b ∘ j.succAbove) =ᵐ[volume] (∅ : Set ℝⁿ) := by
        rw [ae_eq_empty, Real.volume_Icc_pi, prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      rw [setIntegral_congr_set this, setIntegral_congr_set this, setIntegral_empty,
        setIntegral_empty, sub_self]
  · 
    have hlt : ∀ i, a i < b i := fun i => (hle i).lt_of_ne fun hi => hne ⟨i, hi⟩
    exact integral_divergence_of_hasFDerivWithinAt_off_countable_aux₂ ⟨a, b, hlt⟩ f f' s hs Hc
      Hd Hi
theorem integral_divergence_of_hasFDerivWithinAt_off_countable' (hle : a ≤ b)
    (f : Fin (n + 1) → ℝⁿ⁺¹ → E)
    (f' : Fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E) (s : Set ℝⁿ⁺¹)
    (hs : s.Countable) (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ (pi Set.univ fun i => Ioo (a i) (b i)) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' i x (e i)) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' i x (e i)) =
      ∑ i : Fin (n + 1), ((∫ x in face i, f i (frontFace i x)) -
        ∫ x in face i, f i (backFace i x)) :=
  integral_divergence_of_hasFDerivWithinAt_off_countable a b hle (fun x i => f i x)
    (fun x => ContinuousLinearMap.pi fun i => f' i x) s hs (continuousOn_pi.2 Hc)
    (fun x hx => hasFDerivAt_pi.2 (Hd x hx)) Hi
end
theorem integral_divergence_of_hasFDerivWithinAt_off_countable_of_equiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [MeasureSpace F] [BorelSpace F]
    (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
    (he_vol : MeasurePreserving eL volume volume) (f : Fin (n + 1) → F → E)
    (f' : Fin (n + 1) → F → F →L[ℝ] E) (s : Set F) (hs : s.Countable) (a b : F) (hle : a ≤ b)
    (Hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (Hd : ∀ x ∈ interior (Icc a b) \ s, ∀ (i), HasFDerivAt (f i) (f' i x) x) (DF : F → E)
    (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm <| e i)) (Hi : IntegrableOn DF (Icc a b)) :
    ∫ x in Icc a b, DF x =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL b i) x)) -
          ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            f i (eL.symm <| i.insertNth (eL a i) x)) :=
  have he_emb : MeasurableEmbedding eL := eL.toHomeomorph.measurableEmbedding
  have hIcc : eL ⁻¹' Icc (eL a) (eL b) = Icc a b := by
    ext1 x; simp only [Set.mem_preimage, Set.mem_Icc, he_ord]
  have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' Icc a b := by rw [← hIcc, eL.symm_preimage_preimage]
  calc
    ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm <| e i) := by simp only [hDF]
    _ = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm <| e i) := by
      rw [← he_vol.setIntegral_preimage_emb he_emb]
      simp only [hIcc, eL.symm_apply_apply]
    _ = ∑ i : Fin (n + 1),
          ((∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL b i) x)) -
            ∫ x in Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
              f i (eL.symm <| i.insertNth (eL a i) x)) := by
      refine integral_divergence_of_hasFDerivWithinAt_off_countable' (eL a) (eL b)
        ((he_ord _ _).2 hle) (fun i x => f i (eL.symm x))
        (fun i x => f' i (eL.symm x) ∘L (eL.symm : ℝⁿ⁺¹ →L[ℝ] F)) (eL.symm ⁻¹' s)
        (hs.preimage eL.symm.injective) ?_ ?_ ?_
      · exact fun i => (Hc i).comp eL.symm.continuousOn hIcc'.subset
      · refine fun x hx i => (Hd (eL.symm x) ⟨?_, hx.2⟩ i).comp x eL.symm.hasFDerivAt
        rw [← hIcc]
        refine preimage_interior_subset_interior_preimage eL.continuous ?_
        simpa only [Set.mem_preimage, eL.apply_symm_apply, ← pi_univ_Icc,
          interior_pi_set (@finite_univ (Fin _) _), interior_Icc] using hx.1
      · rw [← he_vol.integrableOn_comp_preimage he_emb, hIcc]
        simp [← hDF, Function.comp_def, Hi]
end
open scoped Interval
open ContinuousLinearMap (smulRight)
local macro:arg t:term:max noWs "¹" : term => `(Fin 1 → $t)
local macro:arg t:term:max noWs "²" : term => `(Fin 2 → $t)
theorem integral_eq_of_hasDerivWithinAt_off_countable_of_le (f f' : ℝ → E) {a b : ℝ}
    (hle : a ≤ b) {s : Set ℝ} (hs : s.Countable) (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) (Hi : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a := by
  set e : ℝ ≃L[ℝ] ℝ¹ := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  have e_symm : ∀ x, e.symm x = x 0 := fun x => rfl
  set F' : ℝ → ℝ →L[ℝ] E := fun x => smulRight (1 : ℝ →L[ℝ] ℝ) (f' x)
  have hF' : ∀ x y, F' x y = y • f' x := fun x y => rfl
  calc
    ∫ x in a..b, f' x = ∫ x in Icc a b, f' x := by
      rw [intervalIntegral.integral_of_le hle, setIntegral_congr_set Ioc_ae_eq_Icc]
    _ = ∑ i : Fin 1,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              f (e.symm <| i.insertNth (e a i) x)) := by
      simp only [← interior_Icc] at Hd
      refine
        integral_divergence_of_hasFDerivWithinAt_off_countable_of_equiv e ?_ ?_ (fun _ => f)
          (fun _ => F') s hs a b hle (fun _ => Hc) (fun x hx _ => Hd x hx) _ ?_ ?_
      · exact fun x y => (OrderIso.funUnique (Fin 1) ℝ).symm.le_iff_le
      · exact (volume_preserving_funUnique (Fin 1) ℝ).symm _
      · intro x; rw [Fin.sum_univ_one, hF', e_symm, Pi.single_eq_same, one_smul]
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at Hi
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm
    _ = f b - f a := by
      simp only [e, Fin.sum_univ_one, e_symm]
      have : ∀ c : ℝ, const (Fin 0) c = isEmptyElim := fun c => Subsingleton.elim _ _
      simp [this, volume_pi, Measure.pi_of_empty fun _ : Fin 0 => volume]
theorem integral_eq_of_hasDerivWithinAt_off_countable (f f' : ℝ → E) {a b : ℝ} {s : Set ℝ}
    (hs : s.Countable) (Hc : ContinuousOn f [[a, b]])
    (Hd : ∀ x ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' x) x)
    (Hi : IntervalIntegrable f' volume a b) : ∫ x in a..b, f' x = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
    exact integral_eq_of_hasDerivWithinAt_off_countable_of_le f f' hab hs Hc Hd Hi
  · simp only [uIcc_of_ge hab, min_eq_right hab, max_eq_left hab] at *
    rw [intervalIntegral.integral_symm, neg_eq_iff_eq_neg, neg_sub]
    exact integral_eq_of_hasDerivWithinAt_off_countable_of_le f f' hab hs Hc Hd Hi.symm
theorem integral_divergence_prod_Icc_of_hasFDerivWithinAt_off_countable_of_le (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) -
        ∫ y in a.2..b.2, f (a.1, y) :=
  let e : (ℝ × ℝ) ≃L[ℝ] ℝ² := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  calc
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
        ∑ i : Fin 2,
          ((∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e b i) x)) -
            ∫ x in Icc (e a ∘ i.succAbove) (e b ∘ i.succAbove),
              ![f, g] i (e.symm <| i.insertNth (e a i) x)) := by
      refine integral_divergence_of_hasFDerivWithinAt_off_countable_of_equiv e ?_ ?_ ![f, g]
        ![f', g'] s hs a b hle ?_ (fun x hx => ?_) _ ?_ Hi
      · exact fun x y => (OrderIso.finTwoArrowIso ℝ).symm.le_iff_le
      · exact (volume_preserving_finTwoArrow ℝ).symm _
      · exact Fin.forall_fin_two.2 ⟨Hcf, Hcg⟩
      · rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc] at hx
        exact Fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩
      · intro x; rw [Fin.sum_univ_two]; rfl
    _ = ((∫ y in Icc a.2 b.2, f (b.1, y)) - ∫ y in Icc a.2 b.2, f (a.1, y)) +
          ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) := by
      have : ∀ (a b : ℝ¹) (f : ℝ¹ → E),
          ∫ x in Icc a b, f x = ∫ x in Icc (a 0) (b 0), f fun _ => x := fun a b f ↦ by
        convert (((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) f _).symm
        exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc a b).symm
      simp only [Fin.sum_univ_two, this]
      rfl
    _ = (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
            ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) := by
      simp only [intervalIntegral.integral_of_le hle.1, intervalIntegral.integral_of_le hle.2,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
      abel
theorem integral2_divergence_prod_of_hasFDerivWithinAt_off_countable (f g : ℝ × ℝ → E)
    (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ) (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hcg : ContinuousOn g ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (Hdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
      HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
        ∫ y in a₂..b₂, f (a₁, y) := by
  wlog h₁ : a₁ ≤ b₁ generalizing a₁ b₁
  · specialize this b₁ a₁
    rw [uIcc_comm b₁ a₁, min_comm b₁ a₁, max_comm b₁ a₁] at this
    simp only [intervalIntegral.integral_symm b₁ a₁]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_le h₁))).trans ?_; abel
  wlog h₂ : a₂ ≤ b₂ generalizing a₂ b₂
  · specialize this b₂ a₂
    rw [uIcc_comm b₂ a₂, min_comm b₂ a₂, max_comm b₂ a₂] at this
    simp only [intervalIntegral.integral_symm b₂ a₂, intervalIntegral.integral_neg]
    refine (congr_arg Neg.neg (this Hcf Hcg Hdf Hdg Hi (le_of_not_le h₂))).trans ?_; abel
  simp only [uIcc_of_le h₁, uIcc_of_le h₂, min_eq_left, max_eq_right, h₁, h₂] at Hcf Hcg Hdf Hdg Hi
  calc
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
        ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) := by
      simp only [intervalIntegral.integral_of_le, h₁, h₂,
        setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    _ = ∫ x in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f' x (1, 0) + g' x (0, 1) := (setIntegral_prod _ Hi).symm
    _ = (((∫ x in a₁..b₁, g (x, b₂)) - ∫ x in a₁..b₁, g (x, a₂)) + ∫ y in a₂..b₂, f (b₁, y)) -
          ∫ y in a₂..b₂, f (a₁, y) := by
      rw [Icc_prod_Icc] at *
      apply integral_divergence_prod_Icc_of_hasFDerivWithinAt_off_countable_of_le f g f' g'
        (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s <;> assumption
end MeasureTheory