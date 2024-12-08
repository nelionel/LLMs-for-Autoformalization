import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
open RCLike Submodule Filter
open scoped NNReal ENNReal ComplexConjugate Topology
noncomputable section
variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y
notation "ℓ²(" ι ", " 𝕜 ")" => lp (fun i : ι => 𝕜) 2
namespace lp
theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  refine .of_norm_bounded (fun i => ‖f i‖ * ‖g i‖) (lp.summable_mul ?_ f g) ?_
  · rw [Real.isConjExponent_iff]; norm_num
  intro i
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _
instance instInnerProductSpace : InnerProductSpace 𝕜 (lp G 2) :=
  { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : ℝ≥0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : ℕ) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by
          congr
          funext i
          rw [norm_sq_eq_inner (𝕜 := 𝕜)]
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }
theorem inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ :=
  rfl
theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).hasSum
theorem inner_single_left [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ := by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  convert hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp
theorem inner_single_right [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ := by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)
end lp
namespace OrthogonalFamily
variable [CompleteSpace E] {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)
include hV
protected theorem summable_of_lp (f : lp G 2) :
    Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert (lp.memℓp f).summable _
  · norm_cast
  · norm_num
protected def linearIsometry (hV : OrthogonalFamily 𝕜 G V) : lp G 2 →ₗᵢ[𝕜] E where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using
      tsum_const_smul c (hV.summable_of_lp f)
  norm_map' f := by
    classical
      have H : 0 < (2 : ℝ≥0∞).toReal := by norm_num
      suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal by
        exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
      refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
      convert (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
      ext s
      exact mod_cast (hV.norm_sum f s).symm
protected theorem linearIsometry_apply (f : lp G 2) : hV.linearIsometry f = ∑' i, V i (f i) :=
  rfl
protected theorem hasSum_linearIsometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.linearIsometry f) :=
  (hV.summable_of_lp f).hasSum
@[simp]
protected theorem linearIsometry_apply_single [DecidableEq ι] {i : ι} (x : G i) :
    hV.linearIsometry (lp.single 2 i x) = V i x := by
  rw [hV.linearIsometry_apply, ← tsum_ite_eq i (V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]
protected theorem linearIsometry_apply_dfinsupp_sum_single [DecidableEq ι] [∀ i, DecidableEq (G i)]
    (W₀ : Π₀ i : ι, G i) : hV.linearIsometry (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp
protected theorem range_linearIsometry [∀ i, CompleteSpace (G i)] :
    LinearMap.range hV.linearIsometry.toLinearMap =
      (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (Eventually.of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.isUniformInducing.isComplete_range.isClosed
end OrthogonalFamily
section IsHilbertSum
variable (𝕜 G)
variable [CompleteSpace E] (V : ∀ i, G i →ₗᵢ[𝕜] E) (F : ι → Submodule 𝕜 E)
structure IsHilbertSum : Prop where
  ofSurjective ::
  protected OrthogonalFamily : OrthogonalFamily 𝕜 G V
  protected surjective_isometry : Function.Surjective OrthogonalFamily.linearIsometry
variable {𝕜 G V}
theorem IsHilbertSum.mk [∀ i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
    (hVtotal : ⊤ ≤ (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure) :
    IsHilbertSum 𝕜 G V :=
  { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }
theorem IsHilbertSum.mkInternal [∀ i, CompleteSpace <| F i]
    (hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ)
    (hFtotal : ⊤ ≤ (⨆ i, F i).topologicalClosure) :
    IsHilbertSum 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ :=
  IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)
noncomputable def IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 G V) : E ≃ₗᵢ[𝕜] lp G 2 :=
  LinearIsometryEquiv.symm <|
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : hV.linearIsometryEquiv.symm w = ∑' i, V i (w i) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]
protected theorem IsHilbertSum.hasSum_linearIsometryEquiv_symm (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : HasSum (fun i => V i (w i)) (hV.linearIsometryEquiv.symm w) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]
@[simp]
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_single
    [DecidableEq ι] (hV : IsHilbertSum 𝕜 G V) {i : ι} (x : G i) :
    hV.linearIsometryEquiv.symm (lp.single 2 i x) = V i x := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
    [DecidableEq ι] [∀ i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    hV.linearIsometryEquiv.symm (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp only [map_dfinsupp_sum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]
@[simp]
protected theorem IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
    [DecidableEq ι] [∀ i, DecidableEq (G i)] (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    ((W₀.sum (γ := lp G 2) fun a b ↦ hV.linearIsometryEquiv (V a b)) : ∀ i, G i) = W₀ := by
  rw [← map_dfinsupp_sum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp +contextual [DFinsupp.sum, lp.single_apply]
theorem Orthonormal.isHilbertSum {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    IsHilbertSum 𝕜 (fun _ : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  IsHilbertSum.mk hv.orthogonalFamily (by
    convert hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])
theorem Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    IsHilbertSum 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ := by
  have : ∀ b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq, cond, cond]
  refine Codisjoint.top_le ?_
  exact Submodule.isCompl_orthogonal_of_completeSpace.codisjoint
end IsHilbertSum
section
variable (ι) (𝕜) (E)
structure HilbertBasis where ofRepr ::
  repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)
end
namespace HilbertBasis
instance {ι : Type*} : Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨ofRepr (LinearIsometryEquiv.refl 𝕜 _)⟩
open Classical in
instance instCoeFun : CoeFun (HilbertBasis ι 𝕜 E) fun _ => ι → E where
  coe b i := b.repr.symm (lp.single 2 i (1 : 𝕜))
protected theorem repr_symm_single [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (lp.single 2 i (1 : 𝕜)) = b i := by
  convert rfl
protected theorem repr_self [DecidableEq ι] (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = lp.single 2 i (1 : 𝕜) := by
  simp only [LinearIsometryEquiv.apply_symm_apply]
  convert rfl
protected theorem repr_apply_apply (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
  rw [← b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left]
  simp
@[simp]
protected theorem orthonormal (b : HilbertBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply]
  simp
protected theorem hasSum_repr_symm (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) := by
  classical
  suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv <|
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.two_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) →L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  letI : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (1 : 𝕜) (f i)
  rw [mul_one] at this
  rw [LinearIsometryEquiv.map_smul, b.repr_self, ← this,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm
protected theorem hasSum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.hasSum_repr_symm (b.repr x)
@[simp]
protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  classical
    rw [eq_top_iff]
    rintro x -
    refine mem_closure_of_tendsto (b.hasSum_repr x) (Eventually.of_forall ?_)
    intro s
    simp only [SetLike.mem_coe]
    refine sum_mem ?_
    rintro i -
    refine smul_mem _ _ ?_
    exact subset_span ⟨i, rfl⟩
protected theorem hasSum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫ * ⟪b i, y⟫) ⟪x, y⟫ := by
  convert (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply, b.repr_apply_apply, inner_smul_right, mul_comm]
protected theorem summable_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    Summable fun i => ⟪x, b i⟫ * ⟪b i, y⟫ :=
  (b.hasSum_inner_mul_inner x y).summable
protected theorem tsum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
  (b.hasSum_inner_mul_inner x y).tsum_eq
protected def toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      classical
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)
@[simp]
theorem coe_toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    (b.toOrthonormalBasis : ι → E) = b :=
  OrthonormalBasis.coe_mk _ _
protected theorem hasSum_orthogonalProjection {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : HilbertBasis ι 𝕜 U) (x : E) :
    HasSum (fun i => ⟪(b i : E), x⟫ • b i) (orthogonalProjection U x) := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjection_eq_of_mem_left] using
    b.hasSum_repr (orthogonalProjection U x)
theorem finite_spans_dense [DecidableEq E] (b : HilbertBasis ι 𝕜 E) :
    (⨆ J : Finset ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤ :=
  eq_top_iff.mpr <| b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
      Set.mem_iUnion_of_mem {i} <| Finset.mem_coe.mpr <| Finset.mem_image_of_mem _ <|
      Finset.mem_singleton_self i))
variable [CompleteSpace E]
section
variable {v : ι → E} (hv : Orthonormal 𝕜 v)
include hv
protected def mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.ofRepr <| (hv.isHilbertSum hsp).linearIsometryEquiv
theorem _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one [DecidableEq ι] (h i) :
    (hv.isHilbertSum h).linearIsometryEquiv.symm (lp.single 2 i 1) = v i := by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, LinearIsometry.toSpanSingleton_apply,
    one_smul]
@[simp]
protected theorem coe_mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(HilbertBasis.mk hv hsp) = v := by
  classical
  apply funext <| Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])
@[simp]
protected theorem coe_mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _
protected def _root_.OrthonormalBasis.toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk b.orthonormal <| by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using
      @subset_closure E _ _
end
@[simp]
theorem _root_.OrthonormalBasis.coe_toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (b.toHilbertBasis : ι → E) = b :=
  HilbertBasis.coe_mk _ _
theorem _root_.Orthonormal.exists_hilbertBasis_extension {s : Set E}
    (hs : Orthonormal 𝕜 ((↑) : s → E)) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = ((↑) : w → E) :=
  let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩
variable (𝕜 E)
theorem _root_.exists_hilbertBasis : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩
end HilbertBasis