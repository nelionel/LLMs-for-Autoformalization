import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
open Filter Set
open scoped Topology Classical
variable {a b : ℝ} {f f' : ℝ → ℝ}
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a < m)
    (hmb : m < f' b) : m ∈ f' '' Ioo a b := by
  rcases hab.eq_or_lt with (rfl | hab')
  · exact (lt_asymm hma hmb).elim
  set g : ℝ → ℝ := fun x => f x - m * x
  have hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x := by
    intro x hx
    simpa using (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Icc a b, IsMinOn g (Icc a b) c :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).continuousWithinAt
  have cmem' : c ∈ Ioo a b := by
    rcases cmem.1.eq_or_lt with (rfl | hac)
    · refine absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right ?_ (sub_pos.2 hab'))
        (not_le_of_lt hma)
      have : b - a ∈ posTangentConeAt (Icc a b) a :=
        sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
      simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
        using hc.localize.hasFDerivWithinAt_nonneg (hg a (left_mem_Icc.2 hab)) this
    rcases cmem.2.eq_or_gt with (rfl | hcb)
    · refine absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right ?_ (sub_lt_zero.2 hab'))
        (not_le_of_lt hmb)
      have : a - b ∈ posTangentConeAt (Icc a b) b :=
        sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
        using hc.localize.hasFDerivWithinAt_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hcb⟩
  use c, cmem'
  rw [← sub_eq_zero]
  have : Icc a b ∈ 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.isLocalMin this).hasDerivAt_eq_zero ((hg c cmem).hasDerivAt this)
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : m < f' a)
    (hmb : f' b < m) : m ∈ f' '' Ioo a b :=
  let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩
theorem Set.OrdConnected.image_hasDerivWithinAt {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : OrdConnected (f' '' s) := by
  apply ordConnected_of_Ioo
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩
  rcases le_total a b with hab | hab
  · have : Icc a b ⊆ s := hs.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x <| this hx).mono this) hma
        hmb with
      ⟨c, cmem, hc⟩
    exact ⟨c, this <| Ioo_subset_Icc_self cmem, hc⟩
  · have : Icc b a ⊆ s := hs.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun x hx => (hf x <| this hx).mono this) hmb
        hma with
      ⟨c, cmem, hc⟩
    exact ⟨c, this <| Ioo_subset_Icc_self cmem, hc⟩
theorem Set.OrdConnected.image_derivWithin {s : Set ℝ} (hs : OrdConnected s)
    (hf : DifferentiableOn ℝ f s) : OrdConnected (derivWithin f s '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivWithinAt
theorem Set.OrdConnected.image_deriv {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : OrdConnected (deriv f '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt
theorem Convex.image_hasDerivWithinAt {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : Convex ℝ (f' '' s) :=
  (hs.ordConnected.image_hasDerivWithinAt hf).convex
theorem Convex.image_derivWithin {s : Set ℝ} (hs : Convex ℝ s) (hf : DifferentiableOn ℝ f s) :
    Convex ℝ (derivWithin f s '' s) :=
  (hs.ordConnected.image_derivWithin hf).convex
theorem Convex.image_deriv {s : Set ℝ} (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    Convex ℝ (deriv f '' s) :=
  (hs.ordConnected.image_deriv hf).convex
theorem exists_hasDerivWithinAt_eq_of_ge_of_le (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a ≤ m)
    (hmb : m ≤ f' b) : m ∈ f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩
theorem exists_hasDerivWithinAt_eq_of_le_of_ge (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a ≤ m)
    (hmb : m ≤ f' b) : m ∈ f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩
theorem hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) {m : ℝ} (hf' : ∀ x ∈ s, f' x ≠ m) :
    (∀ x ∈ s, f' x < m) ∨ ∀ x ∈ s, m < f' x := by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact (hs.ordConnected.image_hasDerivWithinAt hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩