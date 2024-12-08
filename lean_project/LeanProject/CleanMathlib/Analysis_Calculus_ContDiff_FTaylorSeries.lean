import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
noncomputable section
open scoped Classical
open ENat NNReal Topology Filter
local notation "∞" => (⊤ : ℕ∞)
open Set Fin Filter Function
universe u uE uF
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s t u : Set E} {f f₁ : E → F} {x : E} {m n N : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}
structure HasFTaylorSeriesUpToOn
  (n : WithTop ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).curry0 = f x
  protected fderivWithin : ∀ m : ℕ, (m : ℕ∞) < n → ∀ x ∈ s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : ∀ m : ℕ, m ≤ n → ContinuousOn (p · m) s
theorem HasFTaylorSeriesUpToOn.zero_eq' (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm
theorem HasFTaylorSeriesUpToOn.congr (h : HasFTaylorSeriesUpToOn n f p s)
    (h₁ : ∀ x ∈ s, f₁ x = f x) : HasFTaylorSeriesUpToOn n f₁ p s := by
  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx
theorem HasFTaylorSeriesUpToOn.mono (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
    HasFTaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩
theorem HasFTaylorSeriesUpToOn.of_le (h : HasFTaylorSeriesUpToOn n f p s) (hmn : m ≤ n) :
    HasFTaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩
theorem HasFTaylorSeriesUpToOn.continuousOn (h : HasFTaylorSeriesUpToOn n f p s) :
    ContinuousOn f s := by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [← (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_continuousOn_iff]
theorem hasFTaylorSeriesUpToOn_zero_iff :
    HasFTaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ ∀ x ∈ s, (p x 0).curry0 = f x := by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm ↦ ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm (zero_le _)
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx ↦
    (continuousMultilinearCurryFin0 𝕜 E F).eq_symm_apply.2 (H.2 x hx)
  rw [continuousOn_congr this, LinearIsometryEquiv.comp_continuousOn_iff]
  exact H.1
theorem hasFTaylorSeriesUpToOn_top_iff_add (hN : ∞ ≤ N) (k : ℕ) :
    HasFTaylorSeriesUpToOn N f p s ↔ ∀ n : ℕ, HasFTaylorSeriesUpToOn (n + k : ℕ) f p s := by
  constructor
  · intro H n
    apply H.of_le (natCast_le_of_coe_top_le_withTop hN _)
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (by norm_cast; omega)
    · intro m _
      apply (H m).cont m (by simp)
theorem hasFTaylorSeriesUpToOn_top_iff (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔ ∀ n : ℕ, HasFTaylorSeriesUpToOn n f p s := by
  simpa using hasFTaylorSeriesUpToOn_top_iff_add hN 0
theorem hasFTaylorSeriesUpToOn_top_iff' (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        ∀ m : ℕ, ∀ x ∈ s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x := by
  refine ⟨fun h => ⟨h.1, fun m => h.2 m (natCast_lt_of_coe_top_le_withTop hN _)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      (h.2 m x hx).continuousWithinAt⟩⟩
theorem HasFTaylorSeriesUpToOn.hasFDerivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : x ∈ s) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x := by
  have A : ∀ y ∈ s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := fun y hy ↦
    (h.zero_eq y hy).symm
  suffices H : HasFDerivWithinAt (continuousMultilinearCurryFin0 𝕜 E F ∘ (p · 0))
    (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x from H.congr A (A x hx)
  rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
  have : ((0 : ℕ) : ℕ∞) < n := zero_lt_one.trans_le hn
  convert h.fderivWithin _ this x hx
  ext y v
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v)
  congr with i
  rw [Unique.eq_default (α := Fin 1) i]
  rfl
theorem HasFTaylorSeriesUpToOn.differentiableOn (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun _x hx => (h.hasFDerivWithinAt hn hx).differentiableWithinAt
theorem HasFTaylorSeriesUpToOn.hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.hasFDerivWithinAt hn (mem_of_mem_nhds hx)).hasFDerivAt hx
theorem HasFTaylorSeriesUpToOn.eventually_hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s)
    (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono fun _y hy => h.hasFDerivAt hn hy
theorem HasFTaylorSeriesUpToOn.differentiableAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hn hx).differentiableAt
theorem hasFTaylorSeriesUpToOn_succ_iff_left {n : ℕ} :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      HasFTaylorSeriesUpToOn n f p s ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y n) (p x n.succ).curryLeft s x) ∧
          ContinuousOn (fun x => p x (n + 1)) s := by
  constructor
  · exact fun h ↦ ⟨h.of_le (mod_cast Nat.le_succ n),
      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (mod_cast h')
      · have : m = n := Nat.eq_of_lt_succ_of_not_lt (mod_cast hm) h'
        rw [this]
        exact h.2.1
    · intro m hm
      by_cases h' : m ≤ n
      · apply h.1.cont m (mod_cast h')
      · have : m = n + 1 := le_antisymm (mod_cast hm) (not_le.1 h')
        rw [this]
        exact h.2.2
#adaptation_note
set_option maxSynthPendingDepth 2 in
theorem HasFTaylorSeriesUpToOn.shift_of_succ
    {n : ℕ} (H : HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s) :
    (HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
      (fun x => (p x).shift)) s := by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : WithTop ℕ∞) < n) x (hx : x ∈ s)
    have A : (m.succ : WithTop ℕ∞) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
      (p x m.succ.succ).curryRight.curryLeft s x
    rw [(continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_hasFDerivWithinAt_iff']
    convert H.fderivWithin _ A x hx
    ext y v
    change p x (m + 2) (snoc (cons y (init v)) (v (last _))) = p x (m + 2) (cons y v)
    rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
  · intro m (hm : (m : WithTop ℕ∞) ≤ n)
    suffices A : ContinuousOn (p · (m + 1)) s from
      (continuousMultilinearCurryRightEquiv' 𝕜 m E F).continuous.comp_continuousOn A
    refine H.cont _ ?_
    rw [Nat.cast_le] at hm ⊢
    exact Nat.succ_le_succ hm
theorem hasFTaylorSeriesUpToOn_succ_nat_iff_right {n : ℕ} :
    HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  constructor
  · intro H
    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
    exact H.shift_of_succ
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m (hm : (m : WithTop ℕ∞) < n.succ) x (hx : x ∈ s)
      cases' m with m
      · exact Hfderiv_zero x hx
      · have A : (m : WithTop ℕ∞) < n := by
          rw [Nat.cast_lt] at hm ⊢
          exact Nat.lt_of_succ_lt_succ hm
        have :
          HasFDerivWithinAt (𝕜 := 𝕜) (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
            ((p x).shift m.succ).curryLeft s x := Htaylor.fderivWithin _ A x hx
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'] at this
        convert this
        ext y v
        change
          (p x (Nat.succ (Nat.succ m))) (cons y v) =
            (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
    · intro m (hm : (m : WithTop ℕ∞) ≤ n.succ)
      cases' m with m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx =>
          (Hfderiv_zero x hx).differentiableWithinAt
        exact this.continuousOn
      · refine (continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_continuousOn_iff.mp ?_
        refine Htaylor.cont _ ?_
        rw [Nat.cast_le] at hm ⊢
        exact Nat.lt_succ_iff.mp hm
theorem hasFTaylorSeriesUpToOn_top_iff_right (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn N (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hasFTaylorSeriesUpToOn_top_iff_add hN 1] at h
    rw [hasFTaylorSeriesUpToOn_top_iff hN]
    exact ⟨(hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).1,
      (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).2.1,
      fun n ↦ (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h n)).2.2⟩
  · apply (hasFTaylorSeriesUpToOn_top_iff_add hN 1).2 (fun n ↦ ?_)
    rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
    exact ⟨h.1, h.2.1, (h.2.2).of_le (m := n) (natCast_le_of_coe_top_le_withTop hN n)⟩
theorem hasFTaylorSeriesUpToOn_succ_iff_right :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  match n with
  | ⊤ => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (⊤ : ℕ∞) => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (n : ℕ) => exact hasFTaylorSeriesUpToOn_succ_nat_iff_right
variable (𝕜)
noncomputable def iteratedFDerivWithin (n : ℕ) (f : E → F) (s : Set E) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)
def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDerivWithin 𝕜 n f s x
variable {𝕜}
@[simp]
theorem iteratedFDerivWithin_zero_apply (m : Fin 0 → E) :
    (iteratedFDerivWithin 𝕜 0 f s x : (Fin 0 → E) → F) m = f x :=
  rfl
theorem iteratedFDerivWithin_zero_eq_comp :
    iteratedFDerivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl
@[simp]
theorem norm_iteratedFDerivWithin_zero : ‖iteratedFDerivWithin 𝕜 0 f s x‖ = ‖f x‖ := by
  rw [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.norm_map]
theorem iteratedFDerivWithin_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl
theorem iteratedFDerivWithin_succ_eq_comp_left {n : ℕ} :
    iteratedFDerivWithin 𝕜 (n + 1) f s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s :=
  rfl
theorem fderivWithin_iteratedFDerivWithin {s : Set E} {n : ℕ} :
    fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F) ∘
        iteratedFDerivWithin 𝕜 (n + 1) f s :=
  rfl
theorem norm_fderivWithin_iteratedFDerivWithin {n : ℕ} :
    ‖fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.norm_map]
theorem iteratedFDerivWithin_succ_apply_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (m : Fin (n + 1) → E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last n)) := by
  induction' n with n IH generalizing x
  · rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp,
      iteratedFDerivWithin_zero_apply, Function.comp_apply,
      LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    rfl
  · let I := (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm
    have A : ∀ y ∈ s, iteratedFDerivWithin 𝕜 n.succ f s y =
        (I ∘ iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) y := fun y hy ↦ by
      ext m
      rw [@IH y hy m]
      rfl
    calc
      (iteratedFDerivWithin 𝕜 (n + 2) f s x : (Fin (n + 2) → E) → F) m =
          (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n.succ f s) s x : E → E[×n + 1]→L[𝕜] F) (m 0)
            (tail m) :=
        rfl
      _ = (fderivWithin 𝕜 (I ∘ iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F) (m 0) (tail m) := by
        rw [fderivWithin_congr A (A x hx)]
      _ = (I ∘ fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F) (m 0) (tail m) := by
        #adaptation_note
        set_option maxSynthPendingDepth 2 in
          simp only [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
        rfl
      _ = (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) s x :
              E → E[×n]→L[𝕜] E →L[𝕜] F) (m 0) (init (tail m)) ((tail m) (last n)) := rfl
      _ = iteratedFDerivWithin 𝕜 (Nat.succ n) (fun y => fderivWithin 𝕜 f s y) s x (init m)
            (m (last (n + 1))) := by
        rw [iteratedFDerivWithin_succ_apply_left, tail_init_eq_init_tail]
        rfl
theorem iteratedFDerivWithin_succ_eq_comp_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 (n + 1) f s x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s)
        x := by
  ext m; rw [iteratedFDerivWithin_succ_apply_right hs hx]; rfl
theorem norm_iteratedFDerivWithin_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, comp_apply, LinearIsometryEquiv.norm_map]
@[simp]
theorem iteratedFDerivWithin_one_apply (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 → E) :
    iteratedFDerivWithin 𝕜 1 f s x m = fderivWithin 𝕜 f s x (m 0) := by
  simp only [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]
  rfl
lemma iteratedFDerivWithin_two_apply (f : E → F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z ∈ s)
    (m : Fin 2 → E) :
    iteratedFDerivWithin 𝕜 2 f s z m = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s z (m 0) (m 1) := by
  simp only [iteratedFDerivWithin_succ_apply_right hs hz]
  rfl
theorem Filter.EventuallyEq.iteratedFDerivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ t =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f t := by
  induction n with
  | zero => exact h.mono fun y hy => DFunLike.ext _ _ fun _ => hy
  | succ n ihn =>
    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
    refine this.mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, hy, (· ∘ ·)]
protected theorem Filter.EventuallyEq.iteratedFDerivWithin (h : f₁ =ᶠ[𝓝[s] x] f) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ s =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s :=
  h.iteratedFDerivWithin' Subset.rfl n
theorem Filter.EventuallyEq.iteratedFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
    (n : ℕ) : iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [EventuallyEq, hx]
  (this.iteratedFDerivWithin' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)
theorem iteratedFDerivWithin_congr (hs : EqOn f₁ f s) (hx : x ∈ s) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).iteratedFDerivWithin_eq (hs hx) _
protected theorem Set.EqOn.iteratedFDerivWithin (hs : EqOn f₁ f s) (n : ℕ) :
    EqOn (iteratedFDerivWithin 𝕜 n f₁ s) (iteratedFDerivWithin 𝕜 n f s) s := fun _x hx =>
  iteratedFDerivWithin_congr hs hx n
theorem iteratedFDerivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ihn =>
    refine (eventually_nhds_nhdsWithin.2 h).mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_nhds, fderivWithin_congr_set' _ hy]
theorem iteratedFDerivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t :=
  iteratedFDerivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n
theorem iteratedFDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (iteratedFDerivWithin_eventually_congr_set h n).self_of_nhds
theorem iteratedFDerivWithin_inter' {n : ℕ} (hu : u ∈ 𝓝[s] x) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _
theorem iteratedFDerivWithin_inter {n : ℕ} (hu : u ∈ 𝓝 x) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)
theorem iteratedFDerivWithin_inter_open {n : ℕ} (hu : IsOpen u) (hx : x ∈ u) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter (hu.mem_nhds hx)
theorem HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (h : HasFTaylorSeriesUpToOn n f p s) {m : ℕ} (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) : p x m = iteratedFDerivWithin 𝕜 m f s x := by
  induction' m with m IH generalizing x
  · rw [h.zero_eq' hx, iteratedFDerivWithin_zero_eq_comp]; rfl
  · have A : (m : ℕ∞) < n := lt_of_lt_of_le (mod_cast lt_add_one m) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFDerivWithin 𝕜 m f s y)
        (ContinuousMultilinearMap.curryLeft (p x (Nat.succ m))) s x :=
      (h.fderivWithin m A x hx).congr (fun y hy => (IH (le_of_lt A) hy).symm)
        (IH (le_of_lt A) hx).symm
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, this.fderivWithin (hs x hx)]
    exact (ContinuousMultilinearMap.uncurry_curryLeft _).symm
@[deprecated (since := "2024-03-28")]
alias HasFTaylorSeriesUpToOn.eq_ftaylor_series_of_uniqueDiffOn :=
  HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
structure HasFTaylorSeriesUpTo
  (n : WithTop ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) : Prop where
  zero_eq : ∀ x, (p x 0).curry0 = f x
  fderiv : ∀ m : ℕ, m < n → ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ m : ℕ, m ≤ n → Continuous fun x => p x m
theorem HasFTaylorSeriesUpTo.zero_eq' (h : HasFTaylorSeriesUpTo n f p) (x : E) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x]
  exact (p x 0).uncurry0_curry0.symm
theorem hasFTaylorSeriesUpToOn_univ_iff :
    HasFTaylorSeriesUpToOn n f p univ ↔ HasFTaylorSeriesUpTo n f p := by
  constructor
  · intro H
    constructor
    · exact fun x => H.zero_eq x (mem_univ x)
    · intro m hm x
      rw [← hasFDerivWithinAt_univ]
      exact H.fderivWithin m hm x (mem_univ x)
    · intro m hm
      rw [continuous_iff_continuousOn_univ]
      exact H.cont m hm
  · intro H
    constructor
    · exact fun x _ => H.zero_eq x
    · intro m hm x _
      rw [hasFDerivWithinAt_univ]
      exact H.fderiv m hm x
    · intro m hm
      rw [← continuous_iff_continuousOn_univ]
      exact H.cont m hm
theorem HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) :
    HasFTaylorSeriesUpToOn n f p s :=
  (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)
theorem HasFTaylorSeriesUpTo.of_le (h : HasFTaylorSeriesUpTo n f p) (hmn : m ≤ n) :
    HasFTaylorSeriesUpTo m f p := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn
@[deprecated (since := "2024-11-07")]
alias HasFTaylorSeriesUpTo.ofLe := HasFTaylorSeriesUpTo.of_le
theorem HasFTaylorSeriesUpTo.continuous (h : HasFTaylorSeriesUpTo n f p) : Continuous f := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [continuous_iff_continuousOn_univ]
  exact h.continuousOn
theorem hasFTaylorSeriesUpTo_zero_iff :
    HasFTaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).curry0 = f x := by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuous_iff_continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]
theorem hasFTaylorSeriesUpTo_top_iff (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpTo N f p ↔ ∀ n : ℕ, HasFTaylorSeriesUpTo n f p := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff hN]
theorem hasFTaylorSeriesUpTo_top_iff' (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpTo N f p ↔
      (∀ x, (p x 0).curry0 = f x) ∧
        ∀ (m : ℕ) (x), HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff' hN, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]
theorem HasFTaylorSeriesUpTo.hasFDerivAt (h : HasFTaylorSeriesUpTo n f p) (hn : 1 ≤ n) (x : E) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x := by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFTaylorSeriesUpToOn_univ_iff.2 h).hasFDerivWithinAt hn (mem_univ _)
theorem HasFTaylorSeriesUpTo.differentiable (h : HasFTaylorSeriesUpTo n f p) (hn : 1 ≤ n) :
    Differentiable 𝕜 f := fun x => (h.hasFDerivAt hn x).differentiableAt
theorem hasFTaylorSeriesUpTo_succ_nat_iff_right {n : ℕ} :
    HasFTaylorSeriesUpTo (n + 1 : ℕ) f p ↔
      (∀ x, (p x 0).curry0 = f x) ∧
        (∀ x, HasFDerivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFTaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x =>
            (p x).shift := by
  simp only [hasFTaylorSeriesUpToOn_succ_nat_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]
@[deprecated (since := "2024-11-07")]
alias hasFTaylorSeriesUpTo_succ_iff_right := hasFTaylorSeriesUpTo_succ_nat_iff_right
variable (𝕜)
noncomputable def iteratedFDeriv (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)
def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDeriv 𝕜 n f x
variable {𝕜}
@[simp]
theorem iteratedFDeriv_zero_apply (m : Fin 0 → E) :
    (iteratedFDeriv 𝕜 0 f x : (Fin 0 → E) → F) m = f x :=
  rfl
theorem iteratedFDeriv_zero_eq_comp :
    iteratedFDeriv 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl
@[simp]
theorem norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖ := by
  rw [iteratedFDeriv_zero_eq_comp, comp_apply, LinearIsometryEquiv.norm_map]
theorem iteratedFDerivWithin_zero_eq : iteratedFDerivWithin 𝕜 0 f s = iteratedFDeriv 𝕜 0 f := rfl
theorem iteratedFDeriv_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      (fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl
theorem iteratedFDeriv_succ_eq_comp_left {n : ℕ} :
    iteratedFDeriv 𝕜 (n + 1) f =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderiv 𝕜 (iteratedFDeriv 𝕜 n f) :=
  rfl
theorem fderiv_iteratedFDeriv {n : ℕ} :
    fderiv 𝕜 (iteratedFDeriv 𝕜 n f) =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F ∘
        iteratedFDeriv 𝕜 (n + 1) f :=
  rfl
theorem tsupport_iteratedFDeriv_subset (n : ℕ) : tsupport (iteratedFDeriv 𝕜 n f) ⊆ tsupport f := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact closure_minimal ((support_comp_subset (LinearIsometryEquiv.map_zero _) _).trans
      subset_closure) isClosed_closure
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact closure_minimal ((support_comp_subset (LinearIsometryEquiv.map_zero _) _).trans
      ((support_fderiv_subset 𝕜).trans IH)) isClosed_closure
theorem support_iteratedFDeriv_subset (n : ℕ) : support (iteratedFDeriv 𝕜 n f) ⊆ tsupport f :=
  subset_closure.trans (tsupport_iteratedFDeriv_subset n)
theorem HasCompactSupport.iteratedFDeriv (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedFDeriv 𝕜 n f) :=
  hf.of_isClosed_subset isClosed_closure (tsupport_iteratedFDeriv_subset n)
theorem norm_fderiv_iteratedFDeriv {n : ℕ} :
    ‖fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.norm_map]
theorem iteratedFDerivWithin_univ {n : ℕ} :
    iteratedFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f := by
  induction n with
  | zero => ext x; simp
  | succ n IH =>
    ext x m
    rw [iteratedFDeriv_succ_apply_left, iteratedFDerivWithin_succ_apply_left, IH, fderivWithin_univ]
theorem HasFTaylorSeriesUpTo.eq_iteratedFDeriv
    (h : HasFTaylorSeriesUpTo n f p) {m : ℕ} (hmn : (m : ℕ∞) ≤ n) (x : E) :
    p x m = iteratedFDeriv 𝕜 m f x := by
  rw [← iteratedFDerivWithin_univ]
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  exact h.eq_iteratedFDerivWithin_of_uniqueDiffOn hmn uniqueDiffOn_univ (mem_univ _)
theorem iteratedFDerivWithin_of_isOpen (n : ℕ) (hs : IsOpen s) :
    EqOn (iteratedFDerivWithin 𝕜 n f s) (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    intro x _
    ext1
    simp only [iteratedFDerivWithin_zero_apply, iteratedFDeriv_zero_apply]
  | succ n IH =>
    intro x hx
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left]
    dsimp
    congr 1
    rw [fderivWithin_of_isOpen hs hx]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hs.mem_nhds hx]
    exact IH
theorem ftaylorSeriesWithin_univ : ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f := by
  ext1 x; ext1 n
  change iteratedFDerivWithin 𝕜 n f univ x = iteratedFDeriv 𝕜 n f x
  rw [iteratedFDerivWithin_univ]
theorem iteratedFDeriv_succ_apply_right {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ, ← fderivWithin_univ]
  exact iteratedFDerivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _
theorem iteratedFDeriv_succ_eq_comp_right {n : ℕ} :
    iteratedFDeriv 𝕜 (n + 1) f x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDeriv 𝕜 n fun y => fderiv 𝕜 f y) x := by
  ext m; rw [iteratedFDeriv_succ_apply_right]; rfl
theorem norm_iteratedFDeriv_fderiv {n : ℕ} :
    ‖iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, comp_apply, LinearIsometryEquiv.norm_map]
@[simp]
theorem iteratedFDeriv_one_apply (m : Fin 1 → E) :
    iteratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply]; rfl
lemma iteratedFDeriv_two_apply (f : E → F) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv 𝕜 2 f z m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1) := by
  simp only [iteratedFDeriv_succ_apply_right]
  rfl