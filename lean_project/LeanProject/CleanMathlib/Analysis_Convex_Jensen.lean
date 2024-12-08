import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
open Finset LinearMap Set
open scoped Classical
open Convex Pointwise
variable {𝕜 E F β ι : Type*}
section Jensen
variable [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommGroup β] [Module 𝕜 E] [Module 𝕜 β]
  [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} {v : 𝕜} {q : E}
theorem ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (t.centerMass w p) ≤ t.centerMass w (f ∘ p) := by
  have hmem' : ∀ i ∈ t, (p i, (f ∘ p) i) ∈ { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]
theorem ConcaveOn.le_map_centerMass (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    t.centerMass w (f ∘ p) ≤ f (t.centerMass w p) :=
  ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hmem : ∀ i ∈ t, p i ∈ s) : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) := by
  simpa only [centerMass, h₁, inv_one, one_smul] using
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i) :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem
lemma ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    f (v • q + ∑ i ∈ t, w i • p i) ≤ v • f q + ∑ i ∈ t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j ∈ insertNone t, W j • P j) ≤ ∑ j ∈ insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using this
lemma ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    v • f q + ∑ i ∈ t, w i • f (p i) ≤ f (v • q + ∑ i ∈ t, w i • p i) :=
  hf.dual.map_add_sum_le h₀ h₁ hmem hv hq
lemma StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) := by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  have : k ∈ t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (mem_cons.not.2 <| not_or_intro (ne_of_apply_ne _ hjk) hj) := by
    simp [insert_erase this, insert_erase ‹j ∈ t›, *]
  clear_value u
  subst ht
  simp only [sum_cons]
  have := h₀ j <| by simp
  have := h₀ k <| by simp
  let c := w j + w k
  have hc : w j / c + w k / c = 1 := by field_simp
  calc f (w j • p j + (w k • p k + ∑ x ∈ u, w x • p x))
    _ = f (c • ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • p x) := by
      congrm f ?_
      match_scalars <;> field_simp
    _ ≤ c • f ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • f (p x) :=
        hf.convexOn.map_add_sum_le (fun i hi ↦ (h₀ _ <| by simp [hi]).le)
          (by simpa [-cons_eq_insert, ← add_assoc] using h₁)
          (forall_of_forall_cons <| forall_of_forall_cons hmem) (by positivity) <| by
           refine hf.1 (hmem _ <| by simp) (hmem _ <| by simp) ?_ ?_ hc <;> positivity
    _ < c • ((w j / c) • f (p j) + (w k / c) • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      gcongr; refine hf.2 (hmem _ <| by simp) (hmem _ <| by simp) hjk ?_ ?_ hc <;> positivity
    _ = (w j • f (p j) + w k • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      match_scalars <;> field_simp
    _ = w j • f (p j) + (w k • f (p k) + ∑ x ∈ u, w x • f (p x)) := by abel_nf
lemma StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) := hf.dual.map_sum_lt h₀ h₁ hmem hp
lemma StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_lt <| hf.map_sum_lt h₀ h₁ hmem this
lemma StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_lt <| hf.lt_map_sum h₀ h₁ hmem this
lemma StrictConvexOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i := by
  constructor
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H : ∀ j ∈ t, p j = p i₀ := by
      intro j hj
      apply hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j ∈ t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j ∈ t, (w j • p i₀) := by rw [sum_smul]
      _ = ∑ j ∈ t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · intro h
    have H : ∀ j ∈ t, w j • f (p j) = w j • f (∑ i ∈ t, w i • p i) := by
      intro j hj
      simp [h j hj]
    rw [sum_congr rfl H, ← sum_smul, h₁, one_smul]
lemma StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i := by
  simpa using hf.neg.map_sum_eq_iff h₀ h₁ hmem
lemma StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := by
  have hw (i) (_ : i ∈ t) : w i • p i ≠ 0 → w i ≠ 0 := by aesop
  have hw' (i) (_ : i ∈ t) : w i • f (p i) ≠ 0 → w i ≠ 0 := by aesop
  rw [← sum_filter_of_ne hw, ← sum_filter_of_ne hw', hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).gt_iff_ne]
  · rwa [sum_filter_ne_zero]
  · simp +contextual [hmem _ _]
lemma StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := hf.dual.map_sum_eq_iff' h₀ h₁ hmem
end Jensen
section MaximumPrinciple
variable [LinearOrderedField 𝕜] [AddCommGroup E] [LinearOrderedAddCommGroup β] [Module 𝕜 E]
  [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {w : ι → 𝕜} {p : ι → E}
  {x y z : E}
theorem ConvexOn.le_sup_of_mem_convexHull {t : Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    f x ≤ t.sup' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) hts).trans
    (centerMass_le_sup hw₀ <| by positivity)
theorem ConvexOn.inf_le_of_mem_convexHull {t : Finset E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    t.inf' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
  hf.dual.le_sup_of_mem_convexHull hts hx
@[deprecated (since := "2024-08-25")]
alias le_sup_of_mem_convexHull := ConvexOn.le_sup_of_mem_convexHull
@[deprecated (since := "2024-08-25")]
alias inf_le_of_mem_convexHull := ConvexOn.inf_le_of_mem_convexHull
lemma ConvexOn.exists_ge_of_centerMass {t : Finset ι} (h : ConvexOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (t.centerMass w p) ≤ f (p i) := by
  set y := t.centerMass w p
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ {i ∈ t | w i ≠ 0}, w i • f y ≤ w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i ∈ t with w i ≠ 0, w i := by rwa [sum_filter_ne_zero]
    refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') ?_
    rw [← sum_smul, ← smul_le_smul_iff_of_pos_left (inv_pos.2 hw'), inv_smul_smul₀ hw'.ne', ←
      centerMass, centerMass_filter_ne_zero]
    exact h.map_centerMass_le hw₀ hw₁ hp
  rw [mem_filter] at hi
  exact ⟨i, hi.1, (smul_le_smul_iff_of_pos_left <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩
lemma ConcaveOn.exists_le_of_centerMass {t : Finset ι} (h : ConcaveOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (p i) ≤ f (t.centerMass w p) := h.dual.exists_ge_of_centerMass hw₀ hw₁ hp
lemma ConvexOn.exists_ge_of_mem_convexHull {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f x ≤ f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi ↦ hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩
lemma ConcaveOn.exists_le_of_mem_convexHull {t : Set E} (hf : ConcaveOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f y ≤ f x := hf.dual.exists_ge_of_mem_convexHull hts hx
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) := by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z := hf.dual.le_max_of_mem_segment hx hy hz
lemma ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : f z ≤ max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz
lemma ConcaveOn.min_le_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : min (f x) (f y) ≤ f z :=
  hf.dual.le_max_of_mem_Icc hx hy hz
lemma ConvexOn.bddAbove_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConvexOn 𝕜 t f) :
    BddAbove (f '' s) → BddAbove (f '' convexHull 𝕜 s) := by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
  exact hxy.trans <| hb <| mem_image_of_mem _ hy
lemma ConcaveOn.bddBelow_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConcaveOn 𝕜 t f) :
    BddBelow (f '' s) → BddBelow (f '' convexHull 𝕜 s) := hf.dual.bddAbove_convexHull hst
end MaximumPrinciple