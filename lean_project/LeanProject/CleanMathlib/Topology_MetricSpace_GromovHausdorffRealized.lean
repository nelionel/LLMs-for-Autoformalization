import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
noncomputable section
universe u v w
open Topology NNReal Set Function TopologicalSpace Filter Metric Quotient BoundedContinuousFunction
open Sum (inl inr)
attribute [local instance] metricSpaceSum
namespace GromovHausdorff
section GromovHausdorffRealized
section Definitions
variable (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
private abbrev ProdSpaceFun : Type _ :=
  (X ⊕ Y) × (X ⊕ Y) → ℝ
private abbrev Cb : Type _ :=
  BoundedContinuousFunction ((X ⊕ Y) × (X ⊕ Y)) ℝ
private def maxVar : ℝ≥0 :=
  2 * ⟨diam (univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : Set Y), diam_nonneg⟩
private theorem one_le_maxVar : 1 ≤ maxVar X Y :=
  calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by simp
    _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> positivity
def candidates : Set (ProdSpaceFun X Y) :=
  { f | (((((∀ x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧
      ∀ x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
      ∀ x y, f (x, y) = f (y, x)) ∧
      ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)) ∧
      ∀ x, f (x, x) = 0) ∧
      ∀ x y, f (x, y) ≤ maxVar X Y }
private def candidatesB : Set (Cb X Y) :=
  { f : Cb X Y | (f : _ → ℝ) ∈ candidates X Y }
end Definitions
section Constructions
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  {f : ProdSpaceFun X Y} {x y z t : X ⊕ Y}
attribute [local instance 10] Classical.inhabited_of_nonempty'
private theorem maxVar_bound [CompactSpace X] [Nonempty X] [CompactSpace Y] [Nonempty Y] :
    dist x y ≤ maxVar X Y :=
  calc
    dist x y ≤ diam (univ : Set (X ⊕ Y)) :=
      dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    _ = diam (range inl ∪ range inr : Set (X ⊕ Y)) := by rw [range_inl_union_range_inr]
    _ ≤ diam (range inl : Set (X ⊕ Y)) + dist (inl default) (inr default) +
        diam (range inr : Set (X ⊕ Y)) :=
      (diam_union (mem_range_self _) (mem_range_self _))
    _ = diam (univ : Set X) + (dist (α := X) default default + 1 + dist (α := Y) default default) +
        diam (univ : Set Y) := by
      rw [isometry_inl.diam_range, isometry_inr.diam_range]
      rfl
    _ = 1 * diam (univ : Set X) + 1 + 1 * diam (univ : Set Y) := by simp
    _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by gcongr <;> norm_num
private theorem candidates_symm (fA : f ∈ candidates X Y) : f (x, y) = f (y, x) :=
  fA.1.1.1.2 x y
private theorem candidates_triangle (fA : f ∈ candidates X Y) : f (x, z) ≤ f (x, y) + f (y, z) :=
  fA.1.1.2 x y z
private theorem candidates_refl (fA : f ∈ candidates X Y) : f (x, x) = 0 :=
  fA.1.2 x
private theorem candidates_nonneg (fA : f ∈ candidates X Y) : 0 ≤ f (x, y) := by
  have : 0 ≤ 2 * f (x, y) :=
    calc
      0 = f (x, x) := (candidates_refl fA).symm
      _ ≤ f (x, y) + f (y, x) := candidates_triangle fA
      _ = f (x, y) + f (x, y) := by rw [candidates_symm fA]
      _ = 2 * f (x, y) := by ring
  linarith
private theorem candidates_dist_inl (fA : f ∈ candidates X Y) (x y : X) :
    f (inl x, inl y) = dist x y :=
  fA.1.1.1.1.1 x y
private theorem candidates_dist_inr (fA : f ∈ candidates X Y) (x y : Y) :
    f (inr x, inr y) = dist x y :=
  fA.1.1.1.1.2 x y
private theorem candidates_le_maxVar (fA : f ∈ candidates X Y) : f (x, y) ≤ maxVar X Y :=
  fA.2 x y
private theorem candidates_dist_bound (fA : f ∈ candidates X Y) :
    ∀ {x y : X ⊕ Y}, f (x, y) ≤ maxVar X Y * dist x y
  | inl x, inl y =>
    calc
      f (inl x, inl y) = dist x y := candidates_dist_inl fA x y
      _ = dist (α := X ⊕ Y) (inl x) (inl y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X ⊕ Y) (inl x) (inl y) := by ring
      _ ≤ maxVar X Y * dist (inl x) (inl y) := by gcongr; exact one_le_maxVar X Y
  | inl x, inr y =>
    calc
      f (inl x, inr y) ≤ maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) := by gcongr; apply Sum.one_le_dist_inl_inr
  | inr x, inl y =>
    calc
      f (inr x, inl y) ≤ maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) := by gcongr; apply Sum.one_le_dist_inl_inr
  | inr x, inr y =>
    calc
      f (inr x, inr y) = dist x y := candidates_dist_inr fA x y
      _ = dist (α := X ⊕ Y) (inr x) (inr y) := by
        rw [@Sum.dist_eq X Y]
        rfl
      _ = 1 * dist (α := X ⊕ Y) (inr x) (inr y) := by ring
      _ ≤ maxVar X Y * dist (inr x) (inr y) := by gcongr; exact one_le_maxVar X Y
private theorem candidates_lipschitz_aux (fA : f ∈ candidates X Y) :
    f (x, y) - f (z, t) ≤ 2 * maxVar X Y * dist (x, y) (z, t) :=
  calc
    f (x, y) - f (z, t) ≤ f (x, t) + f (t, y) - f (z, t) := by gcongr; exact candidates_triangle fA
    _ ≤ f (x, z) + f (z, t) + f (t, y) - f (z, t) := by gcongr; exact candidates_triangle fA
    _ = f (x, z) + f (t, y) := by simp [sub_eq_add_neg, add_assoc]
    _ ≤ maxVar X Y * dist x z + maxVar X Y * dist t y := by
      gcongr <;> apply candidates_dist_bound fA
    _ ≤ maxVar X Y * max (dist x z) (dist t y) + maxVar X Y * max (dist x z) (dist t y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = 2 * maxVar X Y * max (dist x z) (dist y t) := by
      rw [dist_comm t y]
      ring
    _ = 2 * maxVar X Y * dist (x, y) (z, t) := rfl
private theorem candidates_lipschitz (fA : f ∈ candidates X Y) :
    LipschitzWith (2 * maxVar X Y) f := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq, abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA
private theorem closed_candidatesB : IsClosed (candidatesB X Y) := by
  have I1 : ∀ x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    isClosed_eq continuous_eval_const continuous_const
  have I2 : ∀ x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    isClosed_eq continuous_eval_const continuous_const
  have I3 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) = f (y, x) } := fun x y =>
    isClosed_eq continuous_eval_const continuous_eval_const
  have I4 : ∀ x y z, IsClosed { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) } := fun x y z =>
    isClosed_le continuous_eval_const (continuous_eval_const.add continuous_eval_const)
  have I5 : ∀ x, IsClosed { f : Cb X Y | f (x, x) = 0 } := fun x =>
    isClosed_eq continuous_eval_const continuous_const
  have I6 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) ≤ maxVar X Y } := fun x y =>
    isClosed_le continuous_eval_const continuous_const
  have : candidatesB X Y = (((((⋂ (x) (y), { f : Cb X Y | f (@inl X Y x, @inl X Y y) = dist x y }) ∩
      ⋂ (x) (y), { f : Cb X Y | f (@inr X Y x, @inr X Y y) = dist x y }) ∩
      ⋂ (x) (y), { f : Cb X Y | f (x, y) = f (y, x) }) ∩
      ⋂ (x) (y) (z), { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) }) ∩
      ⋂ x, { f : Cb X Y | f (x, x) = 0 }) ∩
      ⋂ (x) (y), { f : Cb X Y | f (x, y) ≤ maxVar X Y } := by
    ext
    simp only [candidatesB, candidates, mem_inter_iff, mem_iInter, mem_setOf_eq]
  rw [this]
  repeat'
    first
      |apply IsClosed.inter _ _
      |apply isClosed_iInter _
      |apply I1 _ _|apply I2 _ _|apply I3 _ _|apply I4 _ _ _|apply I5 _|apply I6 _ _|intro x
def HD (f : Cb X Y) :=
  max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))
theorem HD_below_aux1 {f : Cb X Y} (C : ℝ) {x : X} :
    BddBelow (range fun y : Y => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩
private theorem HD_bound_aux1 [Nonempty Y] (f : Cb X Y) (C : ℝ) :
    BddAbove (range fun x : X => ⨅ y, f (inl x, inr y) + C) := by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun x => ?_⟩
  calc
    ⨅ y, f (inl x, inr y) + C ≤ f (inl x, inr default) + C := ciInf_le (HD_below_aux1 C) default
    _ ≤ Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
theorem HD_below_aux2 {f : Cb X Y} (C : ℝ) {y : Y} :
    BddBelow (range fun x : X => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  ⟨cf + C, forall_mem_range.2 fun _ => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩
private theorem HD_bound_aux2 [Nonempty X] (f : Cb X Y) (C : ℝ) :
    BddAbove (range fun y : Y => ⨅ x, f (inl x, inr y) + C) := by
  obtain ⟨Cf, hCf⟩ := f.isBounded_range.bddAbove
  refine ⟨Cf + C, forall_mem_range.2 fun y => ?_⟩
  calc
    ⨅ x, f (inl x, inr y) + C ≤ f (inl default, inr y) + C := ciInf_le (HD_below_aux2 C) default
    _ ≤ Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
section Nonempty
variable [Nonempty X] [Nonempty Y]
private theorem HD_lipschitz_aux1 (f g : Cb X Y) :
    (⨆ x, ⨅ y, f (inl x, inr y)) ≤ (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g := by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  have Z : (⨆ x, ⨅ y, f (inl x, inr y)) ≤ ⨆ x, ⨅ y, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux1 _ (dist f g)) fun x =>
      ciInf_mono ⟨cf, forall_mem_range.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  have E1 : ∀ x, (⨅ y, g (inl x, inr y)) + dist f g = ⨅ y, g (inl x, inr y) + dist f g := by
    intro x
    refine Monotone.map_ciInf_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · show BddBelow (range fun y : Y => g (inl x, inr y))
      exact ⟨cg, forall_mem_range.2 fun i => Hcg _⟩
  have E2 : (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g = ⨆ x, (⨅ y, g (inl x, inr y)) + dist f g := by
    refine Monotone.map_ciSup_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · simpa using HD_bound_aux1 _ 0
  simpa [E2, E1, Function.comp]
private theorem HD_lipschitz_aux2 (f g : Cb X Y) :
    (⨆ y, ⨅ x, f (inl x, inr y)) ≤ (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g := by
  obtain ⟨cg, hcg⟩ := g.isBounded_range.bddBelow
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  obtain ⟨cf, hcf⟩ := f.isBounded_range.bddBelow
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  have Z : (⨆ y, ⨅ x, f (inl x, inr y)) ≤ ⨆ y, ⨅ x, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux2 _ (dist f g)) fun y =>
      ciInf_mono ⟨cf, forall_mem_range.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  have E1 : ∀ y, (⨅ x, g (inl x, inr y)) + dist f g = ⨅ x, g (inl x, inr y) + dist f g := by
    intro y
    refine Monotone.map_ciInf_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · show BddBelow (range fun x : X => g (inl x, inr y))
      exact ⟨cg, forall_mem_range.2 fun i => Hcg _⟩
  have E2 : (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g = ⨆ y, (⨅ x, g (inl x, inr y)) + dist f g := by
    refine Monotone.map_ciSup_of_continuousAt (continuousAt_id.add continuousAt_const) ?_ ?_
    · intro x y hx
      simpa
    · simpa using HD_bound_aux2 _ 0
  simpa [E2, E1]
private theorem HD_lipschitz_aux3 (f g : Cb X Y) :
    HD f ≤ HD g + dist f g :=
  max_le (le_trans (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_left _ _) _))
    (le_trans (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_right _ _) _))
private theorem HD_continuous : Continuous (HD : Cb X Y → ℝ) :=
  LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)
end Nonempty
variable [CompactSpace X] [CompactSpace Y]
private theorem isCompact_candidatesB : IsCompact (candidatesB X Y) := by
  refine arzela_ascoli₂
      (Icc 0 (maxVar X Y) : Set ℝ) isCompact_Icc (candidatesB X Y) closed_candidatesB ?_ ?_
  · rintro f ⟨x1, x2⟩ hf
    simp only [Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_maxVar hf⟩
  · refine equicontinuous_of_continuity_modulus (fun t => 2 * maxVar X Y * t) ?_ _ ?_
    · have : Tendsto (fun t : ℝ => 2 * (maxVar X Y : ℝ) * t) (𝓝 0) (𝓝 (2 * maxVar X Y * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this
    · rintro x y ⟨f, hf⟩
      exact (candidates_lipschitz hf).dist_le_mul _ _
def candidatesBOfCandidates (f : ProdSpaceFun X Y) (fA : f ∈ candidates X Y) : Cb X Y :=
  BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).continuous⟩
theorem candidatesBOfCandidates_mem (f : ProdSpaceFun X Y) (fA : f ∈ candidates X Y) :
    candidatesBOfCandidates f fA ∈ candidatesB X Y :=
  fA
variable [Nonempty X] [Nonempty Y]
private theorem dist_mem_candidates :
    (fun p : (X ⊕ Y) × (X ⊕ Y) => dist p.1 p.2) ∈ candidates X Y := by
  simp_rw [candidates, Set.mem_setOf_eq, dist_comm, dist_triangle, dist_self, maxVar_bound,
    forall_const, and_true]
  exact ⟨fun x y => rfl, fun x y => rfl⟩
def candidatesBDist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : Cb X Y :=
  candidatesBOfCandidates _ dist_mem_candidates
theorem candidatesBDist_mem_candidatesB :
    candidatesBDist X Y ∈ candidatesB X Y :=
  candidatesBOfCandidates_mem _ _
private theorem candidatesB_nonempty : (candidatesB X Y).Nonempty :=
  ⟨_, candidatesBDist_mem_candidatesB⟩
theorem HD_candidatesBDist_le :
    HD (candidatesBDist X Y) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := by
  refine max_le (ciSup_le fun x => ?_) (ciSup_le fun y => ?_)
  · have A : ⨅ y, candidatesBDist X Y (inl x, inr y) ≤ candidatesBDist X Y (inl x, inr default) :=
      ciInf_le (by simpa using HD_below_aux1 0) default
    have B : dist (inl x) (inr default) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl x) (inr (default : Y)) = dist x (default : X) + 1 + dist default default := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          gcongr <;>
            exact dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    exact le_trans A B
  · have A : ⨅ x, candidatesBDist X Y (inl x, inr y) ≤ candidatesBDist X Y (inl default, inr y) :=
      ciInf_le (by simpa using HD_below_aux2 0) default
    have B : dist (inl default) (inr y) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl (default : X)) (inr y) = dist default default + 1 + dist default y := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          gcongr <;>
            exact dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
    exact le_trans A B
end Constructions
section Consequences
variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]
private theorem exists_minimizer : ∃ f ∈ candidatesB X Y, ∀ g ∈ candidatesB X Y, HD f ≤ HD g :=
  isCompact_candidatesB.exists_isMinOn candidatesB_nonempty HD_continuous.continuousOn
private def optimalGHDist : Cb X Y :=
  Classical.choose (exists_minimizer X Y)
private theorem optimalGHDist_mem_candidatesB : optimalGHDist X Y ∈ candidatesB X Y := by
  cases Classical.choose_spec (exists_minimizer X Y)
  assumption
private theorem HD_optimalGHDist_le (g : Cb X Y) (hg : g ∈ candidatesB X Y) :
    HD (optimalGHDist X Y) ≤ HD g :=
  let ⟨_, Z2⟩ := Classical.choose_spec (exists_minimizer X Y)
  Z2 g hg
def premetricOptimalGHDist : PseudoMetricSpace (X ⊕ Y) where
  dist p q := optimalGHDist X Y (p, q)
  dist_self _ := candidates_refl (optimalGHDist_mem_candidatesB X Y)
  dist_comm _ _ := candidates_symm (optimalGHDist_mem_candidatesB X Y)
  dist_triangle _ _ _ := candidates_triangle (optimalGHDist_mem_candidatesB X Y)
  edist_dist x y := by
    simp only
    congr
    simp only [left_eq_sup]
    exact candidates_nonneg (optimalGHDist_mem_candidatesB X Y)
attribute [local instance] premetricOptimalGHDist
def OptimalGHCoupling : Type _ :=
  @SeparationQuotient (X ⊕ Y) (premetricOptimalGHDist X Y).toUniformSpace.toTopologicalSpace
instance : MetricSpace (OptimalGHCoupling X Y) := by
  unfold OptimalGHCoupling
  infer_instance
def optimalGHInjl (x : X) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inl x)
theorem isometry_optimalGHInjl : Isometry (optimalGHInjl X Y) :=
  Isometry.of_dist_eq fun _ _ => candidates_dist_inl (optimalGHDist_mem_candidatesB X Y) _ _
def optimalGHInjr (y : Y) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inr y)
theorem isometry_optimalGHInjr : Isometry (optimalGHInjr X Y) :=
  Isometry.of_dist_eq fun _ _ => candidates_dist_inr (optimalGHDist_mem_candidatesB X Y) _ _
instance compactSpace_optimalGHCoupling : CompactSpace (OptimalGHCoupling X Y) := ⟨by
  rw [← range_quotient_mk']
  exact isCompact_range (continuous_sum_dom.2
    ⟨(isometry_optimalGHInjl X Y).continuous, (isometry_optimalGHInjr X Y).continuous⟩)⟩
theorem hausdorffDist_optimal_le_HD {f} (h : f ∈ candidatesB X Y) :
    hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤ HD f := by
  refine le_trans (le_of_forall_le_of_dense fun r hr => ?_) (HD_optimalGHDist_le X Y f h)
  have A : ∀ x ∈ range (optimalGHInjl X Y), ∃ y ∈ range (optimalGHInjr X Y), dist x y ≤ r := by
    rintro _ ⟨z, rfl⟩
    have I1 : (⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_left _ _) hr
    have I2 :
        ⨅ y, optimalGHDist X Y (inl z, inr y) ≤ ⨆ x, ⨅ y, optimalGHDist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux1 _ 0) (mem_range_self _)
    have I : ⨅ y, optimalGHDist X Y (inl z, inr y) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    exact ⟨optimalGHInjr X Y z', mem_range_self _, le_of_lt hr'⟩
  refine hausdorffDist_le_of_mem_dist ?_ A ?_
  · inhabit X
    rcases A _ (mem_range_self default) with ⟨y, -, hy⟩
    exact le_trans dist_nonneg hy
  · rintro _ ⟨z, rfl⟩
    have I1 : (⨆ y, ⨅ x, optimalGHDist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    have I2 :
        ⨅ x, optimalGHDist X Y (inl x, inr z) ≤ ⨆ y, ⨅ x, optimalGHDist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux2 _ 0) (mem_range_self _)
    have I : ⨅ x, optimalGHDist X Y (inl x, inr z) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    refine ⟨optimalGHInjl X Y z', mem_range_self _, le_of_lt ?_⟩
    rwa [dist_comm]
end Consequences
end GromovHausdorffRealized
end GromovHausdorff