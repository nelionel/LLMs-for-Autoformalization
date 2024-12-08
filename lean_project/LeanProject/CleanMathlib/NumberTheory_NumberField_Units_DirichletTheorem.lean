import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Units.Basic
open scoped NumberField
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units
variable (K : Type*) [Field K]
namespace NumberField.Units.dirichletUnitTheorem
open scoped Classical
open Finset
variable {K}
section NumberField
variable [NumberField K]
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some
variable (K)
def _root_.NumberField.Units.logEmbedding :
    Additive ((𝓞 K)ˣ) →+ ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
{ toFun := fun x w => mult w.val * Real.log (w.val ↑x.toMul)
  map_zero' := by simp; rfl
  map_add' := fun _ _ => by simp [Real.log_mul, mul_add]; rfl }
variable {K}
@[simp]
theorem logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    (logEmbedding K (Additive.ofMul x)) w = mult w.val * Real.log (w.val x) := rfl
theorem sum_logEmbedding_component (x : (𝓞 K)ˣ) :
    ∑ w, logEmbedding K (Additive.ofMul x) w =
      - mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := congr_arg Real.log (prod_eq_abs_norm (x : K))
  rw [Units.norm, Rat.cast_one, Real.log_one, Real.log_prod] at h
  · simp_rw [Real.log_pow] at h
    rw [← insert_erase (mem_univ w₀), sum_insert (not_mem_erase w₀ univ), add_comm,
      add_eq_zero_iff_eq_neg] at h
    convert h using 1
    · refine (sum_subtype _ (fun w => ?_) (fun w => (mult w) * (Real.log (w (x : K))))).symm
      exact ⟨ne_of_mem_erase, fun h => mem_erase_of_ne_of_mem h (mem_univ w)⟩
    · norm_num
  · exact fun w _ => pow_ne_zero _ (AbsoluteValue.ne_zero _ (coe_ne_zero x))
end NumberField
theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 ≤ w x)]
  · simp only [ne_eq, map_eq_zero, coe_ne_zero x, not_false_eq_true]
  · refine (ne_of_gt ?_)
    rw [mult]; split_ifs <;> norm_num
variable [NumberField K]
theorem logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices -mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← sum_logEmbedding_component, sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [logEmbedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]
theorem logEmbedding_component_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖logEmbedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ w₀}) : |logEmbedding K (Additive.ofMul x) w| ≤ r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)
theorem log_le_of_logEmbedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r)
    (h : ‖logEmbedding K (Additive.ofMul x)‖ ≤ r) (w : InfinitePlace K) :
    |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  have tool : ∀ x : ℝ, 0 ≤ x → x ≤ mult w * x := fun x hx => by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (sum_logEmbedding_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (sum_le_card_nsmul univ _ _
        (fun w _ => logEmbedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp [card_univ]
  · have hyp := logEmbedding_component_le hr h ⟨w, hw⟩
    rw [logEmbedding_component, abs_mul, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)
variable (K)
noncomputable def _root_.NumberField.Units.unitLattice :
    Submodule ℤ ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  Submodule.map (logEmbedding K).toIntLinearMap ⊤
theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice K : Set ({ w : InfinitePlace K // w ≠ w₀} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_le r 0
  · convert Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
        ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      refine (Set.Finite.image (logEmbedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w => (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (log_le_of_logEmbedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
    refine (Embeddings.finite_of_norm_le K ℂ
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩
section span_top
open NumberField.mixedEmbedding NNReal
variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)
include hB in
theorem seq_next {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ y : 𝓞 K, y ≠ 0 ∧
      (∀ w, w ≠ w₁ → w y < w x) ∧
      |Algebra.norm ℚ (y : K)| ≤ B := by
  have hx' := RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K → ℝ≥0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by norm_num)⟩
  suffices ∀ w, w ≠ w₁ → f w ≠ 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := g)
      (by rw [convexBodyLT_volume]; convert hB; exact congr_arg ((↑) : NNReal → ENNReal) h_gprod)
    refine ⟨y, h_ynz, fun w hw => (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := ℝ), Rat.cast_natCast]
      calc
        _ = ∏ w : InfinitePlace K, w (algebraMap _ K y) ^ mult w :=
          (prod_eq_abs_norm (algebraMap _ K y)).symm
        _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ mult w := by gcongr with w; exact (h_yle w).le
        _ ≤ (B : ℝ) := by
          simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
          exact le_of_eq (congr_arg toReal h_gprod)
    · refine div_lt_self ?_ (by norm_num)
      exact pos_iff.mpr hx'
  intro _ _
  rw [ne_eq, Nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, not_or]
  exact ⟨hx', by norm_num⟩
def seq : ℕ → { x : 𝓞 K // x ≠ 0 }
  | 0 => ⟨1, by norm_num⟩
  | n + 1 =>
    ⟨(seq_next K w₁ hB (seq n).prop).choose, (seq_next K w₁ hB (seq n).prop).choose_spec.1⟩
theorem seq_ne_zero (n : ℕ) : algebraMap (𝓞 K) K (seq K w₁ hB n) ≠ 0 :=
  RingOfIntegers.coe_ne_zero_iff.mpr (seq K w₁ hB n).prop
theorem seq_decreasing {n m : ℕ} (h : n < m) (w : InfinitePlace K) (hw : w ≠ w₁) :
    w (algebraMap (𝓞 K) K (seq K w₁ hB m)) < w (algebraMap (𝓞 K) K (seq K w₁ hB n)) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr)
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
theorem seq_norm_le (n : ℕ) :
    Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ≤ B := by
  cases n with
  | zero =>
      have : 1 ≤ B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
      exact (seq_next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2
theorem exists_unit (w₁ : InfinitePlace K) :
    ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m, n < m ∧
      (Ideal.span ({ (seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw => Real.log_neg ?_ ?_⟩
    · exact pos_iff.mpr (coe_ne_zero _)
    · calc
        _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m) * (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹) := by
          rw [← congr_arg (algebraMap (𝓞 K) K) hu.choose_spec, mul_comm, map_mul (algebraMap _ _),
          ← mul_assoc, inv_mul_cancel₀ (seq_ne_zero K w₁ hB n), one_mul]
      _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m)) * w (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹ :=
        _root_.map_mul _ _ _
      _ < 1 := by
        rw [map_inv₀, mul_inv_lt_iff₀' (pos_iff.mpr (seq_ne_zero K w₁ hB n)), mul_one]
        exact seq_decreasing K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem (t := {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ B})
    (fun n ↦ ?_) (Ideal.finite_setOf_absNorm_le B)
  rw [Set.mem_setOf_eq, Ideal.absNorm_span_singleton]
  exact seq_norm_le K w₁ hB n
theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ)) = ⊤ := by
  refine le_antisymm le_top ?_
  let B := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  let v := fun w : { w : InfinitePlace K // w ≠ w₀ } =>
    logEmbedding K (Additive.ofMul (exists_unit K w).choose)
  suffices B.det v ≠ 0 by
    rw [← isUnit_iff_ne_zero, ← is_basis_iff_det] at this
    rw [← this.2]
    refine  Submodule.span_monotone fun _ ⟨w, hw⟩ ↦ ⟨(exists_unit K w).choose, trivial, hw⟩
  rw [Basis.det_apply]
  refine det_ne_zero_of_sum_col_lt_diag (fun w => ?_)
  simp_rw [Real.norm_eq_abs, B, Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
  rw [← sub_pos, sum_congr rfl (fun x hx => abs_of_neg ?_), sum_neg_distrib, sub_neg_eq_add,
    sum_erase_eq_sub (mem_univ _), ← add_comm_sub]
  · refine add_pos_of_nonneg_of_pos ?_ ?_
    · rw [sub_nonneg]
      exact le_abs_self _
    · rw [sum_logEmbedding_component (exists_unit K w).choose]
      refine mul_pos_of_neg_of_neg ?_ ((exists_unit K w).choose_spec _ w.prop.symm)
      rw [mult]; split_ifs <;> norm_num
  · refine mul_neg_of_pos_of_neg ?_ ((exists_unit K w).choose_spec x ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff_val.not.mp (ne_of_mem_erase hx)
end span_top
end dirichletUnitTheorem
section statements
variable [NumberField K]
open scoped Classical
open dirichletUnitTheorem Module
def rank : ℕ := Fintype.card (InfinitePlace K) - 1
instance instDiscrete_unitLattice : DiscreteTopology (unitLattice K) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by norm_num)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert unitLattice_inter_ball_finite K 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ => ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩
instance instZLattice_unitLattice : IsZLattice ℝ (unitLattice K) where
  span_top := unitLattice_span_eq_top K
protected theorem finrank_eq_rank :
    finrank ℝ ({w : InfinitePlace K // w ≠ w₀} → ℝ) = Units.rank K := by
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]
@[simp]
theorem unitLattice_rank :
    finrank ℤ (unitLattice K) = Units.rank K := by
  rw [← Units.finrank_eq_rank, ZLattice.rank ℝ]
def logEmbeddingQuot :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) →+ ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  MonoidHom.toAdditive' <|
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicative' (logEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicative'_apply_apply, ofAdd_eq_one,
          ← logEmbedding_eq_zero_iff])).toMonoidHom
@[simp]
theorem logEmbeddingQuot_apply (x : (𝓞 K)ˣ) :
    logEmbeddingQuot K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl
theorem logEmbeddingQuot_injective :
    Function.Injective (logEmbeddingQuot K) := by
  unfold logEmbeddingQuot
  intro _ _ h
  simp_rw [MonoidHom.toAdditive'_apply_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
  exact (EmbeddingLike.apply_eq_iff_eq _).mp <| (QuotientGroup.kerLift_injective _).eq_iff.mp h
#adaptation_note
set_option maxSynthPendingDepth 2 
def logEmbeddingEquiv :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) ≃ₗ[ℤ] (unitLattice K) :=
  LinearEquiv.ofBijective ((logEmbeddingQuot K).codRestrict (unitLattice K)
    (Quotient.ind fun _ ↦ logEmbeddingQuot_apply K _ ▸
      Submodule.mem_map_of_mem trivial)).toIntLinearMap
    ⟨fun _ _ ↦ by
      rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.codRestrict_apply,
        AddMonoidHom.codRestrict_apply, Subtype.mk.injEq]
      apply logEmbeddingQuot_injective K, fun ⟨a, ⟨b, _, ha⟩⟩ ↦ ⟨⟦b⟧, by simpa using ha⟩⟩
@[simp]
theorem logEmbeddingEquiv_apply (x : (𝓞 K)ˣ) :
    logEmbeddingEquiv K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl
instance : Module.Free ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
  Module.Free.of_equiv (logEmbeddingEquiv K).symm
instance : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
  Module.Finite.equiv (logEmbeddingEquiv K).symm
instance : Module.Finite ℤ (Additive (𝓞 K)ˣ) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (torsion K)), ← Module.finite_def]
    infer_instance
  · rw [inf_of_le_right le_top, AddMonoidHom.coe_toIntLinearMap_ker, MonoidHom.coe_toAdditive_ker,
      QuotientGroup.ker_mk', Submodule.fg_iff_add_subgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup, ← AddGroup.fg_iff_addSubgroup_fg]
    have : Finite (Subgroup.toAddSubgroup (torsion K)) := (inferInstance : Finite (torsion K))
    exact AddGroup.fg_of_finite
instance : Monoid.FG (𝓞 K)ˣ := by
  rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
  infer_instance
theorem rank_modTorsion :
    Module.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K := by
  rw [← LinearEquiv.finrank_eq (logEmbeddingEquiv K).symm, unitLattice_rank]
def basisModTorsion : Basis (Fin (rank K)) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
  Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex, rank_modTorsion, Fintype.card_fin])
def basisUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  (basisModTorsion K).map (logEmbeddingEquiv K)
def fundSystem : Fin (rank K) → (𝓞 K)ˣ :=
  fun i => Quotient.out ((basisModTorsion K i).toMul:)
theorem fundSystem_mk (i : Fin (rank K)) :
    Additive.ofMul (QuotientGroup.mk (fundSystem K i)) = (basisModTorsion K i) := by
  simp_rw [fundSystem, Equiv.apply_eq_iff_eq_symm_apply, Additive.ofMul_symm_eq, Quotient.out_eq']
theorem logEmbedding_fundSystem (i : Fin (rank K)) :
    logEmbedding K (Additive.ofMul (fundSystem K i)) = basisUnitLattice K i := by
  rw [basisUnitLattice, Basis.map_apply, ← fundSystem_mk, logEmbeddingEquiv_apply]
theorem fun_eq_repr {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) → ℤ} (hζ : ζ ∈ torsion K)
    (h : x = ζ * ∏ i, (fundSystem K i) ^ (f i)) :
    f = (basisModTorsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f, ← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
          rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hζ, one_mul,
            QuotientGroup.mk_prod, ofMul_prod]; rfl
    _ = ∑ i, (f i) • (basisModTorsion K i) := by
          simp_rw [fundSystem, QuotientGroup.out_eq', ofMul_toMul]
theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) : ∃! ζe : torsion K × (Fin (rank K) → ℤ),
    x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) := by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ ∈ torsion K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ofMul_eq_zero,
      ofMul_mul, ofMul_inv, QuotientGroup.mk_prod, ofMul_prod]
    simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, fundSystem, QuotientGroup.out_eq']
    rw [add_eq_zero_iff_eq_neg, neg_neg]
    exact ((basisModTorsion K).sum_repr (Additive.ofMul ↑x)).symm
  refine ⟨⟨⟨ζ, h_tors⟩, ((basisModTorsion K).repr (Additive.ofMul ↑x) : Fin (rank K) → ℤ)⟩, ?_, ?_⟩
  · simp only [ζ, _root_.inv_mul_cancel_right]
  · rintro ⟨⟨ζ', h_tors'⟩, η⟩ hf
    simp only [ζ, ← fun_eq_repr K h_tors' hf, Prod.mk.injEq, Subtype.mk.injEq, and_true]
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]
end statements
end NumberField.Units