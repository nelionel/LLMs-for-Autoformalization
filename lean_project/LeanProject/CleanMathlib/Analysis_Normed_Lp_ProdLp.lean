import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.WithLp
open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal
noncomputable section
variable (p : ℝ≥0∞) (𝕜 α β : Type*)
namespace WithLp
section algebra
variable {p 𝕜 α β}
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable (x y : WithLp p (α × β)) (c : 𝕜)
@[simp]
theorem zero_fst : (0 : WithLp p (α × β)).fst = 0 :=
  rfl
@[simp]
theorem zero_snd : (0 : WithLp p (α × β)).snd = 0 :=
  rfl
@[simp]
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl
@[simp]
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl
@[simp]
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl
@[simp]
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl
@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl
@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl
variable [Module 𝕜 α] [Module 𝕜 β]
@[simp]
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl
@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl
end algebra
section equiv
variable {p α β}
@[simp]
theorem equiv_fst (x : WithLp p (α × β)) : (WithLp.equiv p (α × β) x).fst = x.fst :=
  rfl
@[simp]
theorem equiv_snd (x : WithLp p (α × β)) : (WithLp.equiv p (α × β) x).snd = x.snd :=
  rfl
@[simp]
theorem equiv_symm_fst (x : α × β) : ((WithLp.equiv p (α × β)).symm x).fst = x.fst :=
  rfl
@[simp]
theorem equiv_symm_snd (x : α × β) : ((WithLp.equiv p (α × β)).symm x).snd = x.snd :=
  rfl
end equiv
section DistNorm
section EDist
variable [EDist α] [EDist β]
open scoped Classical in
instance instProdEDist : EDist (WithLp p (α × β)) where
  edist f g :=
    if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)
variable {p α β}
@[simp]
theorem prod_edist_eq_card (f g : WithLp 0 (α × β)) :
    edist f g =
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1) := by
  convert if_pos rfl
theorem prod_edist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
theorem prod_edist_eq_sup (f g : WithLp ∞ (α × β)) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := rfl
end EDist
section EDistProp
variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]
theorem prod_edist_self (f : WithLp p (α × β)) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]
theorem prod_edist_comm (f g : WithLp p (α × β)) : edist f g = edist g f := by
  classical
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]
end EDistProp
section Dist
variable [Dist α] [Dist β]
open scoped Classical in
instance instProdDist : Dist (WithLp p (α × β)) where
  dist f g :=
    if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)
variable {p α β}
theorem prod_dist_eq_card (f g : WithLp 0 (α × β)) : dist f g =
    (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1) := by
  convert if_pos rfl
theorem prod_dist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
theorem prod_dist_eq_sup (f g : WithLp ∞ (α × β)) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := rfl
end Dist
section Norm
variable [Norm α] [Norm β]
open scoped Classical in
instance instProdNorm : Norm (WithLp p (α × β)) where
  norm f :=
    if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
variable {p α β}
@[simp]
theorem prod_norm_eq_card (f : WithLp 0 (α × β)) :
    ‖f‖ = (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1) := by
  convert if_pos rfl
theorem prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := rfl
theorem prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
end Norm
end DistNorm
section Aux
variable [hp : Fact (1 ≤ p)]
def prodPseudoEMetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) where
  edist_self := prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [prod_edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) ≤
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr <;> apply edist_triangle
        _ ≤
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton, reduceCtorEq] at this
          exact this
attribute [local instance] WithLp.prodPseudoEMetricAux
variable {α β}
theorem prod_sup_edist_ne_top_aux [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp ∞ (α × β)) :
    edist f.fst g.fst ⊔ edist f.snd g.snd ≠ ⊤ :=
  ne_of_lt <| by simp [edist, PseudoMetricSpace.edist_dist]
variable (α β)
abbrev prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · exact prod_sup_edist_ne_top_aux f g
      · rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
        refine ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_of_lt ?_)
        simp [ENNReal.add_lt_top, ENNReal.rpow_lt_top_of_nonneg, edist_ne_top] )
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [prod_edist_eq_sup, prod_dist_eq_sup]
      refine le_antisymm (sup_le ?_ ?_) ?_
      · rw [← ENNReal.ofReal_le_iff_le_toReal (prod_sup_edist_ne_top_aux f g),
          ← PseudoMetricSpace.edist_dist]
        exact le_sup_left
      · rw [← ENNReal.ofReal_le_iff_le_toReal (prod_sup_edist_ne_top_aux f g),
          ← PseudoMetricSpace.edist_dist]
        exact le_sup_right
      · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
        · simp only [le_sup_iff, dist_nonneg, or_self]
        · simp [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_le_ofReal]
    · have h1 : edist f.fst g.fst ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      have h2 : edist f.snd g.snd ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [prod_edist_eq_add (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        prod_dist_eq_add (zero_lt_one.trans_le h), ← ENNReal.toReal_add h1 h2]
attribute [local instance] WithLp.prodPseudoMetricAux
theorem prod_lipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (WithLp.equiv p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    simp only [edist, forall_prop_of_true, one_mul, ENNReal.coe_one, sup_le_iff]
    constructor
    · calc
        edist x.fst y.fst ≤ (edist x.fst y.fst ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_right]
    · calc
        edist x.snd y.snd ≤ (edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_left]
theorem prod_antilipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 ≤ 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos, ENNReal.toReal_div 1 p]
    simp only [edist, ← one_div, ENNReal.one_toReal]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) ≤
          (edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) ^ p.toReal +
          edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr <;> simp [edist]
      _ = (2 ^ (1 / p.toReal) : ℝ≥0) * edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) := by
        simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel,
          ENNReal.rpow_one, ENNReal.coe_rpow_of_nonneg _ nonneg, coe_ofNat]
theorem prod_aux_uniformity_eq [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (WithLp p (α × β)) = 𝓤[instUniformSpaceProd] := by
  have A : IsUniformInducing (WithLp.equiv p (α × β)) :=
    (prod_antilipschitzWith_equiv_aux p α β).isUniformInducing
      (prod_lipschitzWith_equiv_aux p α β).uniformContinuous
  have : (fun x : WithLp p (α × β) × WithLp p (α × β) =>
    ((WithLp.equiv p (α × β)) x.fst, (WithLp.equiv p (α × β)) x.snd)) = id := by
    ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]
theorem prod_aux_cobounded_eq [PseudoMetricSpace α] [PseudoMetricSpace β] :
    cobounded (WithLp p (α × β)) = @cobounded _ Prod.instBornology :=
  calc
    cobounded (WithLp p (α × β)) = comap (WithLp.equiv p (α × β)) (cobounded _) :=
      le_antisymm (prod_antilipschitzWith_equiv_aux p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_equiv_aux p α β).comap_cobounded_le
    _ = _ := comap_id
end Aux
section TopologicalSpace
variable [TopologicalSpace α] [TopologicalSpace β]
instance instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β)) :=
  instTopologicalSpaceProd
@[continuity]
theorem prod_continuous_equiv : Continuous (WithLp.equiv p (α × β)) :=
  continuous_id
@[continuity]
theorem prod_continuous_equiv_symm : Continuous (WithLp.equiv p (α × β)).symm :=
  continuous_id
variable [T0Space α] [T0Space β]
instance instProdT0Space : T0Space (WithLp p (α × β)) :=
  Prod.instT0Space
end TopologicalSpace
section UniformSpace
variable [UniformSpace α] [UniformSpace β]
instance instProdUniformSpace : UniformSpace (WithLp p (α × β)) :=
  instUniformSpaceProd
theorem prod_uniformContinuous_equiv : UniformContinuous (WithLp.equiv p (α × β)) :=
  uniformContinuous_id
theorem prod_uniformContinuous_equiv_symm : UniformContinuous (WithLp.equiv p (α × β)).symm :=
  uniformContinuous_id
variable [CompleteSpace α] [CompleteSpace β]
instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  CompleteSpace.prod
end UniformSpace
instance instProdBornology [Bornology α] [Bornology β] : Bornology (WithLp p (α × β)) :=
  Prod.instBornology
section ContinuousLinearEquiv
variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]
@[simps! (config := .asFn) apply symm_apply]
protected def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_equiv _ _ _
  continuous_invFun := prod_continuous_equiv_symm _ _ _
end ContinuousLinearEquiv
variable [hp : Fact (1 ≤ p)]
instance instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) :=
  (prodPseudoEMetricAux p α β).replaceUniformity (prod_aux_uniformity_eq p α β).symm
instance instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (WithLp p (α × β)) :=
  EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))
instance instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_aux_uniformity_eq p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_aux_cobounded_eq p α β).symm sᶜ
instance instProdMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (WithLp p (α × β)) :=
  MetricSpace.ofT0PseudoMetricSpace _
variable {p α β}
theorem prod_nndist_eq_add [PseudoMetricSpace α] [PseudoMetricSpace β]
    (hp : p ≠ ∞) (x y : WithLp p (α × β)) :
    nndist x y = (nndist x.fst y.fst ^ p.toReal + nndist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _
theorem prod_nndist_eq_sup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β)) :
    nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_sup _ _
variable (p α β)
theorem prod_lipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (WithLp.equiv p (α × β)) :=
  prod_lipschitzWith_equiv_aux p α β
theorem prod_antilipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (α × β)) :=
  prod_antilipschitzWith_equiv_aux p α β
theorem prod_infty_equiv_isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (WithLp.equiv ∞ (α × β)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_equiv ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_equiv ∞ α β x y)
instance instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (WithLp p (α × β)) where
  dist_eq x y := by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm]
      rfl
instance instProdNormedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (WithLp p (α × β)) :=
  { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace = instProdUniformSpace p α β :=
  rfl
example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toBornology = instProdBornology p α β :=
  rfl
section norm_of
variable {p α β}
theorem prod_norm_eq_of_nat [Norm α] [Norm β] (n : ℕ) (h : p = n) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_nat, eq_self_iff_true, Finset.sum_congr,
    prod_norm_eq_add this]
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
theorem prod_nnnorm_eq_add (hp : p ≠ ∞) (f : WithLp p (α × β)) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]
theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔  ‖f.snd‖₊ := by
  ext
  norm_cast
@[simp] theorem prod_nnnorm_equiv (f : WithLp ∞ (α × β)) : ‖WithLp.equiv ⊤ _ f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_sup, Prod.nnnorm_def', equiv_fst, equiv_snd]
@[simp] theorem prod_nnnorm_equiv_symm (f : α × β) : ‖(WithLp.equiv ⊤ _).symm f‖₊ = ‖f‖₊ :=
  (prod_nnnorm_equiv _).symm
@[simp] theorem prod_norm_equiv (f : WithLp ∞ (α × β)) : ‖WithLp.equiv ⊤ _ f‖ = ‖f‖ :=
  congr_arg NNReal.toReal <| prod_nnnorm_equiv f
@[simp] theorem prod_norm_equiv_symm (f : α × β) : ‖(WithLp.equiv ⊤ _).symm f‖ = ‖f‖ :=
  (prod_norm_equiv _).symm
theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
  norm_cast
theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L2 x
theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [prod_nnnorm_eq_of_L2, NNReal.sq_sqrt]
theorem prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    dist x y = √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2]
  rfl
theorem prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L2 _ _
theorem prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : ℝ) := by
  simp [prod_edist_eq_add]
end norm_of
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
section Single
@[simp]
theorem nnnorm_equiv_symm_fst (x : α) :
    ‖(WithLp.equiv p (α × β)).symm (x, 0)‖₊ = ‖x‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
@[simp]
theorem nnnorm_equiv_symm_snd (y : β) :
    ‖(WithLp.equiv p (α × β)).symm (0, y)‖₊ = ‖y‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
@[simp]
theorem norm_equiv_symm_fst (x : α) : ‖(WithLp.equiv p (α × β)).symm (x, 0)‖ = ‖x‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_fst p α β x
@[simp]
theorem norm_equiv_symm_snd (y : β) : ‖(WithLp.equiv p (α × β)).symm (0, y)‖ = ‖y‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_snd p α β y
@[simp]
theorem nndist_equiv_symm_fst (x₁ x₂ : α) :
    nndist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← WithLp.equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_fst]
@[simp]
theorem nndist_equiv_symm_snd (y₁ y₂ : β) :
    nndist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← WithLp.equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_snd]
@[simp]
theorem dist_equiv_symm_fst (x₁ x₂ : α) :
    dist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      dist x₁ x₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_fst p α β x₁ x₂
@[simp]
theorem dist_equiv_symm_snd (y₁ y₂ : β) :
    dist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      dist y₁ y₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_snd p α β y₁ y₂
@[simp]
theorem edist_equiv_symm_fst (x₁ x₂ : α) :
    edist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      edist x₁ x₂ := by
  simp only [edist_nndist, nndist_equiv_symm_fst p α β x₁ x₂]
@[simp]
theorem edist_equiv_symm_snd (y₁ y₂ : β) :
    edist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      edist y₁ y₂ := by
  simp only [edist_nndist, nndist_equiv_symm_snd p α β y₁ y₂]
end Single
section BoundedSMul
variable [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [BoundedSMul 𝕜 α] [BoundedSMul 𝕜 β]
instance instProdBoundedSMul : BoundedSMul 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_equiv, WithLp.equiv_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one, mul_add,
        ← NNReal.mul_rpow, ← NNReal.mul_rpow]
      exact add_le_add
        (NNReal.rpow_le_rpow (nnnorm_smul_le _ _) hp0.le)
        (NNReal.rpow_le_rpow (nnnorm_smul_le _ _) hp0.le)
variable {𝕜 p α β}
def prodEquivₗᵢ : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  __ := WithLp.equiv ∞ (α × β)
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' := prod_norm_equiv
end BoundedSMul
section NormedSpace
instance instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] :
    NormedSpace 𝕜 (WithLp p (α × β)) where
  norm_smul_le := norm_smul_le
end NormedSpace
end WithLp