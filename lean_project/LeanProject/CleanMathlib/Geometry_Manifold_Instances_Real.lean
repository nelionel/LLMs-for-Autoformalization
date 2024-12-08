import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section
open Set Function
open scoped Manifold ContDiff
def EuclideanHalfSpace (n : ℕ) [NeZero n] : Type :=
  { x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0 }
def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Fin n) // ∀ i : Fin n, 0 ≤ x i }
section
variable {n : ℕ}
instance [NeZero n] : TopologicalSpace (EuclideanHalfSpace n) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (EuclideanQuadrant n) :=
  instTopologicalSpaceSubtype
instance [NeZero n] : Inhabited (EuclideanHalfSpace n) :=
  ⟨⟨0, le_rfl⟩⟩
instance : Inhabited (EuclideanQuadrant n) :=
  ⟨⟨0, fun _ => le_rfl⟩⟩
@[ext]
theorem EuclideanQuadrant.ext (x y : EuclideanQuadrant n) (h : x.1 = y.1) : x = y :=
  Subtype.eq h
@[ext]
theorem EuclideanHalfSpace.ext [NeZero n] (x y : EuclideanHalfSpace n)
    (h : x.1 = y.1) : x = y :=
  Subtype.eq h
theorem range_euclideanHalfSpace (n : ℕ) [NeZero n] :
    (range fun x : EuclideanHalfSpace n => x.val) = { y | 0 ≤ y 0 } :=
  Subtype.range_val
@[deprecated (since := "2024-04-05")] alias range_half_space := range_euclideanHalfSpace
open ENNReal in
@[simp]
theorem interior_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    interior { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a < y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change interior (f ⁻¹' Ici a) = f ⁻¹' Ioi a
  rw [f.interior_preimage, interior_Ici]
  apply Function.surjective_eval
@[deprecated (since := "2024-11-12")] alias interior_halfspace := interior_halfSpace
open ENNReal in
@[simp]
theorem closure_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a ≤ y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change closure (f ⁻¹' Ici a) = f ⁻¹' Ici a
  rw [f.closure_preimage, closure_Ici]
  apply Function.surjective_eval
@[deprecated (since := "2024-11-12")] alias closure_halfspace := closure_halfSpace
open ENNReal in
@[simp]
theorem closure_open_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | a < y i } = { y | a ≤ y i } := by
  let f : (Π _ : Fin n, ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change closure (f ⁻¹' Ioi a) = f ⁻¹' Ici a
  rw [f.closure_preimage, closure_Ioi]
  apply Function.surjective_eval
@[deprecated (since := "2024-11-12")] alias closure_open_halfspace := closure_open_halfSpace
open ENNReal in
@[simp]
theorem frontier_halfSpace {n : ℕ} (p : ℝ≥0∞) (a : ℝ) (i : Fin n) :
    frontier { y : PiLp p (fun _ : Fin n ↦ ℝ) | a ≤ y i } = { y | a = y i } := by
  rw [frontier, closure_halfSpace, interior_halfSpace]
  ext y
  simpa only [mem_diff, mem_setOf_eq, not_lt] using antisymm_iff
@[deprecated (since := "2024-11-12")] alias frontier_halfspace := frontier_halfSpace
theorem range_euclideanQuadrant (n : ℕ) :
    (range fun x : EuclideanQuadrant n => x.val) = { y | ∀ i : Fin n, 0 ≤ y i } :=
  Subtype.range_val
@[deprecated (since := "2024-04-05")] alias range_quadrant := range_euclideanQuadrant
end
def modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) where
  toFun := Subtype.val
  invFun x := ⟨update x 0 (max (x 0) 0), by simp [le_refl]⟩
  source := univ
  target := { x | 0 ≤ x 0 }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨xval, xprop⟩ _ => by
    rw [Subtype.mk_eq_mk, update_eq_iff]
    exact ⟨max_eq_left xprop, fun i _ => rfl⟩
  right_inv' _ hx := update_eq_iff.2 ⟨max_eq_left hx, fun _ _ => rfl⟩
  source_eq := rfl
  uniqueDiffOn' := by
    have : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.pi (Fin n) (fun _ => ℝ) _ _ fun i (_ : i ∈ ({0} : Set (Fin n))) =>
        uniqueDiffOn_Ici 0
    simpa only [singleton_pi] using this
  target_subset_closure_interior := by simp
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by
    exact (continuous_id.update 0 <| (continuous_apply 0).max continuous_const).subtype_mk _
def modelWithCornersEuclideanQuadrant (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n) where
  toFun := Subtype.val
  invFun x := ⟨fun i => max (x i) 0, fun i => by simp only [le_refl, or_true, le_max_iff]⟩
  source := univ
  target := { x | ∀ i, 0 ≤ x i }
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := by ext i; simp only [Subtype.coe_mk, x.2 i, max_eq_left]
  right_inv' x hx := by ext1 i; simp only [hx i, max_eq_left]
  source_eq := rfl
  uniqueDiffOn' := by
    have this : UniqueDiffOn ℝ _ :=
      UniqueDiffOn.univ_pi (Fin n) (fun _ => ℝ) _ fun _ => uniqueDiffOn_Ici 0
    simpa only [pi_univ_Ici] using this
  target_subset_closure_interior := by
    have : {x : EuclideanSpace ℝ (Fin n) | ∀ (i : Fin n), 0 ≤ x i}
      = Set.pi univ (fun i ↦ Ici 0) := by aesop
    simp only [this, interior_pi_set finite_univ]
    rw [closure_pi_set]
    simp
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun i => (continuous_id.max continuous_const).comp (continuous_apply i)) _
scoped[Manifold]
  notation "𝓡 " n =>
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
scoped[Manifold]
  notation "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n))
lemma range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    range (𝓡∂ n) = { y | 0 ≤ y 0 } := range_euclideanHalfSpace n
lemma interior_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    interior (range (𝓡∂ n)) = { y | 0 < y 0 } := by
  calc interior (range (𝓡∂ n))
    _ = interior ({ y | 0 ≤ y 0}) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 < y 0 } := interior_halfSpace _ _ _
lemma frontier_range_modelWithCornersEuclideanHalfSpace (n : ℕ) [NeZero n] :
    frontier (range (𝓡∂ n)) = { y | 0 = y 0 } := by
  calc frontier (range (𝓡∂ n))
    _ = frontier ({ y | 0 ≤ y 0 }) := by
      congr!
      apply range_euclideanHalfSpace
    _ = { y | 0 = y 0 } := frontier_halfSpace 2 _ _
def IccLeftChart (x y : ℝ) [h : Fact (x < y)] :
    PartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | z.val < y }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun := fun z : Icc x y => ⟨fun _ => z.val - x, sub_nonneg.mpr z.property.1⟩
  invFun z := ⟨min (z.val 0 + x) y, by simp [le_refl, z.prop, le_of_lt h.out]⟩
  map_source' := by simp only [imp_self, sub_lt_sub_iff_right, mem_setOf_eq, forall_true_iff]
  map_target' := by
    simp only [min_lt_iff, mem_setOf_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_setOf_eq, mem_Icc] at hz h'z
    simp only [hz, min_eq_left, sub_add_cancel]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext i
    dsimp at hz h'z
    have A : x + z 0 ≤ y := by linarith
    rw [Subsingleton.elim i 0]
    simp only [A, add_comm, add_sub_cancel_left, min_eq_left]
  open_source :=
    haveI : IsOpen { z : ℝ | z < y } := isOpen_Iio
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@continuous_apply (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (_ : Fin 1) => z - x :=
      Continuous.sub (continuous_pi fun _ => continuous_id) continuous_const
    exact this.comp continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => min (z + x) y :=
      (continuous_id.add continuous_const).min continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val
def IccRightChart (x y : ℝ) [h : Fact (x < y)] :
    PartialHomeomorph (Icc x y) (EuclideanHalfSpace 1) where
  source := { z : Icc x y | x < z.val }
  target := { z : EuclideanHalfSpace 1 | z.val 0 < y - x }
  toFun z := ⟨fun _ => y - z.val, sub_nonneg.mpr z.property.2⟩
  invFun z :=
    ⟨max (y - z.val 0) x, by simp [le_refl, z.prop, le_of_lt h.out, sub_eq_add_neg]⟩
  map_source' := by simp only [imp_self, mem_setOf_eq, sub_lt_sub_iff_left, forall_true_iff]
  map_target' := by
    simp only [lt_max_iff, mem_setOf_eq]; intro z hz; left
    linarith
  left_inv' := by
    rintro ⟨z, hz⟩ h'z
    simp only [mem_setOf_eq, mem_Icc] at hz h'z
    simp only [hz, sub_eq_add_neg, max_eq_left, add_add_neg_cancel'_right, neg_add_rev, neg_neg]
  right_inv' := by
    rintro ⟨z, hz⟩ h'z
    rw [Subtype.mk_eq_mk]
    funext i
    dsimp at hz h'z
    have A : x ≤ y - z 0 := by linarith
    rw [Subsingleton.elim i 0]
    simp only [A, sub_sub_cancel, max_eq_left]
  open_source :=
    haveI : IsOpen { z : ℝ | x < z } := isOpen_Ioi
    this.preimage continuous_subtype_val
  open_target := by
    have : IsOpen { z : ℝ | z < y - x } := isOpen_Iio
    have : IsOpen { z : EuclideanSpace ℝ (Fin 1) | z 0 < y - x } :=
      this.preimage (@continuous_apply (Fin 1) (fun _ => ℝ) _ 0)
    exact this.preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have : Continuous fun (z : ℝ) (_ : Fin 1) => y - z :=
      continuous_const.sub (continuous_pi fun _ => continuous_id)
    exact this.comp continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    have A : Continuous fun z : ℝ => max (y - z) x :=
      (continuous_const.sub continuous_id).max continuous_const
    have B : Continuous fun z : EuclideanSpace ℝ (Fin 1) => z 0 := continuous_apply 0
    exact (A.comp B).comp continuous_subtype_val
instance IccChartedSpace (x y : ℝ) [h : Fact (x < y)] :
    ChartedSpace (EuclideanHalfSpace 1) (Icc x y) where
  atlas := {IccLeftChart x y, IccRightChart x y}
  chartAt z := if z.val < y then IccLeftChart x y else IccRightChart x y
  mem_chart_source z := by
    by_cases h' : z.val < y
    · simp only [h', if_true]
      exact h'
    · simp only [h', if_false]
      apply lt_of_lt_of_le h.out
      simpa only [not_lt] using h'
  chart_mem_atlas z := by by_cases h' : (z : ℝ) < y <;> simp [h']
instance Icc_smoothManifoldWithCorners (x y : ℝ) [Fact (x < y)] :
    SmoothManifoldWithCorners (𝓡∂ 1) (Icc x y) := by
  have M : ContDiff ℝ ∞ (show EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      from fun z i => -z i + (y - x)) :=
    contDiff_id.neg.add contDiff_const
  apply smoothManifoldWithCorners_of_contDiffOn
  intro e e' he he'
  simp only [atlas, mem_singleton_iff, mem_insert_iff] at he he'
  rcases he with (rfl | rfl) <;> rcases he' with (rfl | rfl)
  · 
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
  · 
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨⟨z, hz₀⟩, rfl⟩⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, update_same,
      max_eq_left, hz₀, lt_sub_iff_add_lt, mfld_simps] at hz₁ hz₂
    rw [min_eq_left hz₁.le, lt_add_iff_pos_left] at hz₂
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, *, PiLp.add_apply,
      PiLp.neg_apply, max_eq_left, min_eq_left hz₁.le, update_same, mfld_simps]
    abel
  · 
    apply M.contDiffOn.congr
    rintro _ ⟨⟨hz₁, hz₂⟩, ⟨z, hz₀⟩, rfl⟩
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, max_lt_iff,
      update_same, max_eq_left hz₀, mfld_simps] at hz₁ hz₂
    rw [lt_sub_comm] at hz₁
    ext i
    rw [Subsingleton.elim i 0]
    simp only [modelWithCornersEuclideanHalfSpace, IccLeftChart, IccRightChart, PiLp.add_apply,
      PiLp.neg_apply, update_same, max_eq_left, hz₀, hz₁.le, mfld_simps]
    abel
  ·
    exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1
section
instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1) := by infer_instance
instance : SmoothManifoldWithCorners (𝓡∂ 1) (Icc (0 : ℝ) 1) := by infer_instance
end