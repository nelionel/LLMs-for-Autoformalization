import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.MetricSpace.HausdorffDistance
noncomputable section
open QuotientAddGroup Metric Set Topology NNReal
variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
noncomputable instance normOnQuotient (S : AddSubgroup M) : Norm (M ⧸ S) where
  norm x := sInf (norm '' { m | mk' S m = x })
theorem AddSubgroup.quotient_norm_eq {S : AddSubgroup M} (x : M ⧸ S) :
    ‖x‖ = sInf (norm '' { m : M | (m : M ⧸ S) = x }) :=
  rfl
theorem QuotientAddGroup.norm_eq_infDist {S : AddSubgroup M} (x : M ⧸ S) :
    ‖x‖ = infDist 0 { m : M | (m : M ⧸ S) = x } := by
  simp only [AddSubgroup.quotient_norm_eq, infDist_eq_iInf, sInf_image', dist_zero_left]
theorem QuotientAddGroup.norm_mk {S : AddSubgroup M} (x : M) :
    ‖(x : M ⧸ S)‖ = infDist x S := by
  rw [norm_eq_infDist, ← infDist_image (IsometryEquiv.subLeft x).isometry,
    IsometryEquiv.subLeft_apply, sub_zero, ← IsometryEquiv.preimage_symm]
  congr 1 with y
  simp only [mem_preimage, IsometryEquiv.subLeft_symm_apply, mem_setOf_eq, QuotientAddGroup.eq,
    neg_add, neg_neg, neg_add_cancel_right, SetLike.mem_coe]
theorem image_norm_nonempty {S : AddSubgroup M} (x : M ⧸ S) :
    (norm '' { m | mk' S m = x }).Nonempty :=
  .image _ <| Quot.exists_rep x
theorem bddBelow_image_norm (s : Set M) : BddBelow (norm '' s) :=
  ⟨0, forall_mem_image.2 fun _ _ ↦ norm_nonneg _⟩
theorem isGLB_quotient_norm {S : AddSubgroup M} (x : M ⧸ S) :
    IsGLB (norm '' { m | mk' S m = x }) (‖x‖) :=
  isGLB_csInf (image_norm_nonempty x) (bddBelow_image_norm _)
theorem quotient_norm_neg {S : AddSubgroup M} (x : M ⧸ S) : ‖-x‖ = ‖x‖ := by
  simp only [AddSubgroup.quotient_norm_eq]
  congr 1 with r
  constructor <;> { rintro ⟨m, hm, rfl⟩; use -m; simpa [neg_eq_iff_eq_neg] using hm }
theorem quotient_norm_sub_rev {S : AddSubgroup M} (x y : M ⧸ S) : ‖x - y‖ = ‖y - x‖ := by
  rw [← neg_sub, quotient_norm_neg]
theorem quotient_norm_mk_le (S : AddSubgroup M) (m : M) : ‖mk' S m‖ ≤ ‖m‖ :=
  csInf_le (bddBelow_image_norm _) <| Set.mem_image_of_mem _ rfl
theorem quotient_norm_mk_le' (S : AddSubgroup M) (m : M) : ‖(m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S m
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = sInf ((‖m + ·‖) '' S) := by
  rw [mk'_apply, norm_mk, sInf_image', ← infDist_image isometry_neg, image_neg_eq_neg,
    neg_coe_set (H := S), infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]
theorem quotient_norm_nonneg (S : AddSubgroup M) (x : M ⧸ S) : 0 ≤ ‖x‖ :=
  Real.sInf_nonneg <| forall_mem_image.2 fun _ _ ↦ norm_nonneg _
theorem norm_mk_nonneg (S : AddSubgroup M) (m : M) : 0 ≤ ‖mk' S m‖ :=
  quotient_norm_nonneg S _
theorem quotient_norm_eq_zero_iff (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = 0 ↔ m ∈ closure (S : Set M) := by
  rw [mk'_apply, norm_mk, ← mem_closure_iff_infDist_zero]
  exact ⟨0, S.zero_mem⟩
theorem QuotientAddGroup.norm_lt_iff {S : AddSubgroup M} {x : M ⧸ S} {r : ℝ} :
    ‖x‖ < r ↔ ∃ m : M, ↑m = x ∧ ‖m‖ < r := by
  rw [isGLB_lt_iff (isGLB_quotient_norm _), exists_mem_image]
  rfl
theorem norm_mk_lt {S : AddSubgroup M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, mk' S m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_lt_iff.1 <| lt_add_of_pos_right _ hε
theorem norm_mk_lt' (S : AddSubgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖m + s‖ < ‖mk' S m‖ + ε := by
  obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ‖n‖ < ‖mk' S m‖ + ε⟩ :=
    norm_mk_lt (QuotientAddGroup.mk' S m) hε
  erw [eq_comm, QuotientAddGroup.eq] at hn
  use -m + n, hn
  rwa [add_neg_cancel_left]
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  rcases And.intro (mk_surjective x) (mk_surjective y) with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  simp only [← mk'_apply, ← map_add, quotient_norm_mk_eq, sInf_image']
  refine le_ciInf_add_ciInf fun a b ↦ ?_
  refine ciInf_le_of_le ⟨0, forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (a + b) ?_
  exact (congr_arg norm (add_add_add_comm _ _ _ _)).trans_le (norm_add_le _ _)
theorem norm_mk_zero (S : AddSubgroup M) : ‖(0 : M ⧸ S)‖ = 0 := by
  erw [quotient_norm_eq_zero_iff]
  exact subset_closure S.zero_mem
theorem norm_mk_eq_zero (S : AddSubgroup M) (hS : IsClosed (S : Set M)) (m : M)
    (h : ‖mk' S m‖ = 0) : m ∈ S := by rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h
theorem quotient_nhd_basis (S : AddSubgroup M) :
    (𝓝 (0 : M ⧸ S)).HasBasis (fun ε ↦ 0 < ε) fun ε ↦ { x | ‖x‖ < ε } := by
  have : ∀ ε : ℝ, mk '' ball (0 : M) ε = { x : M ⧸ S | ‖x‖ < ε } := by
    refine fun ε ↦ Set.ext <| forall_mk.2 fun x ↦ ?_
    rw [ball_zero_eq, mem_setOf_eq, norm_lt_iff, mem_image]
    exact exists_congr fun _ ↦ and_comm
  rw [← QuotientAddGroup.mk_zero, nhds_eq, ← funext this]
  exact .map _ Metric.nhds_basis_ball
noncomputable instance AddSubgroup.seminormedAddCommGroupQuotient (S : AddSubgroup M) :
    SeminormedAddCommGroup (M ⧸ S) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    refine le_trans ?_ (quotient_norm_add_le _ _ _)
    exact (congr_arg norm (sub_add_sub_cancel _ _ _).symm).le
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  toUniformSpace := TopologicalAddGroup.toUniformSpace (M ⧸ S)
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_zero', ((quotient_nhd_basis S).comap _).eq_biInf]
    simp only [dist, quotient_norm_sub_rev (Prod.fst _), preimage_setOf_eq]
example (S : AddSubgroup M) :
    (instTopologicalSpaceQuotient : TopologicalSpace <| M ⧸ S) =
      S.seminormedAddCommGroupQuotient.toUniformSpace.toTopologicalSpace :=
  rfl
noncomputable instance AddSubgroup.normedAddCommGroupQuotient (S : AddSubgroup M)
    [IsClosed (S : Set M)] : NormedAddCommGroup (M ⧸ S) :=
  { AddSubgroup.seminormedAddCommGroupQuotient S, MetricSpace.ofT0PseudoMetricSpace _ with }
example (S : AddSubgroup M) [IsClosed (S : Set M)] :
    S.seminormedAddCommGroupQuotient = NormedAddCommGroup.toSeminormedAddCommGroup :=
  rfl
namespace AddSubgroup
open NormedAddGroupHom
noncomputable def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) :=
  { QuotientAddGroup.mk' S with
    bound' := ⟨1, fun m => by simpa [one_mul] using quotient_norm_mk_le _ m⟩ }
@[simp]
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  Quot.mk_surjective
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [quotient_norm_mk_le']
theorem _root_.QuotientAddGroup.norm_lift_apply_le {S : AddSubgroup M} (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ S, f x = 0) (x : M ⧸ S) : ‖lift S f.toAddMonoidHom hf x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_gt with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt, ← lt_div_iff₀' h, norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_le (le_opNorm f x)
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) ≠ univ) :
    ‖S.normedMk‖ = 1 := by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : ∃ x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx ↦ ?_
    exact (norm_nonneg _).lt_of_ne' <| mt (quotient_norm_eq_zero_iff S x).1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le S.normedMk (fun x ↦ (eq_zero_iff x).2) x
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 := by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x ∈ S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk, ← SetLike.mem_coe, h]
    trivial
  rw [ker_normedMk] at hker
  simp only [(quotient_norm_eq_zero_iff S x).mpr hker, normedMk.apply, zero_mul, le_rfl]
end AddSubgroup
namespace NormedAddGroupHom
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }
theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl
theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N)
    (h : g.comp S.normedMk = f) : g = lift S f hf := by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩
theorem IsQuotient.norm_lift {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : ℝ} (hε : 0 < ε)
    (n : N) : ∃ m : M, f m = n ∧ ‖m‖ < ‖n‖ + ε := by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact ⟨m + x, by rw [map_add, (NormedAddGroupHom.mem_ker f x).mp hx, add_zero], by
    rwa [hquot.norm]⟩
theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ ≤ ‖m‖ := by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩
theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) :
    ‖lift S f hf‖ ≤ ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖lift S f hf‖ ≤ c :=
  (norm_lift_le S f hf).trans fb
theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _
end NormedAddGroupHom
section Submodule
variable {R : Type*} [Ring R] [Module R M] (S : Submodule R M)
instance Submodule.Quotient.seminormedAddCommGroup : SeminormedAddCommGroup (M ⧸ S) :=
  AddSubgroup.seminormedAddCommGroupQuotient S.toAddSubgroup
instance Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] :
    NormedAddCommGroup (M ⧸ S) :=
  @AddSubgroup.normedAddCommGroupQuotient _ _ S.toAddSubgroup hS
instance Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S) :=
  QuotientAddGroup.completeSpace M S.toAddSubgroup
nonrec theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S.toAddSubgroup m
instance Submodule.Quotient.instBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [BoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] :
    BoundedSMul 𝕜 (M ⧸ S) :=
  .of_norm_smul_le fun k x =>
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, exists_prop, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
      calc
        _ ≤ ‖k‖ * ‖a‖ := (quotient_norm_mk_le S.toAddSubgroup (k • a)).trans (norm_smul_le k a)
        _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
instance Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where
  norm_smul_le := norm_smul_le
end Submodule
section Ideal
variable {R : Type*} [SeminormedCommRing R] (I : Ideal R)
nonrec theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ :=
  quotient_norm_mk_le I.toAddSubgroup r
instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where
  dist_eq := dist_eq_norm
  mul_comm := _root_.mul_comm
  norm_mul x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, exists_prop, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
      Ideal.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }
variable (𝕜 : Type*) [NormedField 𝕜]
instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }
end Ideal