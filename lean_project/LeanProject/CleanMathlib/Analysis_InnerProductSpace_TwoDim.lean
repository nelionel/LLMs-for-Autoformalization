import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Data.Complex.Orientation
import Mathlib.Tactic.LinearCombination
noncomputable section
open scoped RealInnerProductSpace ComplexConjugate
open Module
lemma FiniteDimensional.of_fact_finrank_eq_two {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 2)] : FiniteDimensional K V :=
  .of_fact_finrank_eq_succ 1
attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two
@[deprecated (since := "2024-02-02")]
alias FiniteDimensional.finiteDimensional_of_fact_finrank_eq_two :=
  FiniteDimensional.of_fact_finrank_eq_two
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))
namespace Orientation
irreducible_def areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  let z : E [⋀^Fin 0]→ₗ[ℝ] ℝ ≃ₗ[ℝ] ℝ :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : E [⋀^Fin 1]→ₗ[ℝ] ℝ →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (E [⋀^Fin 0]→ₗ[ℝ] ℝ) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap (R' := ℝ) o.volumeForm
local notation "ω" => o.areaForm
theorem areaForm_to_volumeForm (x y : E) : ω x y = o.volumeForm ![x, y] := by simp [areaForm]
@[simp]
theorem areaForm_apply_self (x : E) : ω x x = 0 := by
  rw [areaForm_to_volumeForm]
  refine o.volumeForm.map_eq_zero_of_eq ![x, x] ?_ (?_ : (0 : Fin 2) ≠ 1)
  · simp
  · norm_num
theorem areaForm_swap (x y : E) : ω x y = -ω y x := by
  simp only [areaForm_to_volumeForm]
  convert o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) ≠ 1)
  · ext i
    fin_cases i <;> rfl
  · norm_num
@[simp]
theorem areaForm_neg_orientation : (-o).areaForm = -o.areaForm := by
  ext x y
  simp [areaForm_to_volumeForm]
def areaForm' : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) ∘ₗ o.areaForm)
@[simp]
theorem areaForm'_apply (x : E) :
    o.areaForm' x = LinearMap.toContinuousLinearMap (o.areaForm x) :=
  rfl
theorem abs_areaForm_le (x y : E) : |ω x y| ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]
theorem areaForm_le (x y : E) : ω x y ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]
theorem abs_areaForm_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ‖x‖ * ‖y‖ := by
  rw [o.areaForm_to_volumeForm, o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [Fin.prod_univ_succ]
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp_all
  · simpa using h
  · simpa [real_inner_comm] using h
  · simp_all
theorem areaForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).areaForm x y =
    o.areaForm (φ.symm x) (φ.symm y) := by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]
theorem areaForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.areaForm (φ x) (φ y) = o.areaForm x y := by
  convert o.areaForm_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]
  · simp
  · simp
irreducible_def rightAngleRotationAux₁ : E →ₗ[ℝ] E :=
  let to_dual : E ≃ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm
  ↑to_dual.symm ∘ₗ ω
@[simp]
theorem inner_rightAngleRotationAux₁_left (x y : E) : ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y := by
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearIsometryEquiv.toLinearEquiv_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  norm_cast
@[simp]
theorem inner_rightAngleRotationAux₁_right (x y : E) :
    ⟪x, o.rightAngleRotationAux₁ y⟫ = -ω x y := by
  rw [real_inner_comm]
  simp [o.areaForm_swap y x]
def rightAngleRotationAux₂ : E →ₗᵢ[ℝ] E :=
  { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      dsimp
      refine le_antisymm ?_ ?_
      · cases' eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h h
        · rw [← h]
          positivity
        refine le_of_mul_le_mul_right ?_ h
        rw [← real_inner_self_eq_norm_mul_norm, o.inner_rightAngleRotationAux₁_left]
        exact o.areaForm_le x (o.rightAngleRotationAux₁ x)
      · let K : Submodule ℝ E := ℝ ∙ x
        have : Nontrivial Kᗮ := by
          apply nontrivial_of_finrank_pos (R := ℝ)
          have : finrank ℝ K ≤ Finset.card {x} := by
            rw [← Set.toFinset_singleton]
            exact finrank_span_le_card ({x} : Set E)
          have : Finset.card {x} = 1 := Finset.card_singleton x
          have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal
          have : finrank ℝ E = 2 := Fact.out
          linarith
        obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
        have hw' : ⟪x, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
        have hw : (w : E) ≠ 0 := fun h => hw₀ (Submodule.coe_eq_zero.mp h)
        refine le_of_mul_le_mul_right ?_ (by rwa [norm_pos_iff] : 0 < ‖(w : E)‖)
        rw [← o.abs_areaForm_of_orthogonal hw']
        rw [← o.inner_rightAngleRotationAux₁_left x w]
        exact abs_real_inner_le_norm (o.rightAngleRotationAux₁ x) w }
@[simp]
theorem rightAngleRotationAux₁_rightAngleRotationAux₁ (x : E) :
    o.rightAngleRotationAux₁ (o.rightAngleRotationAux₁ x) = -x := by
  apply ext_inner_left ℝ
  intro y
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right, ← o.inner_rightAngleRotationAux₁_left, this,
    inner_neg_right]
irreducible_def rightAngleRotation : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofLinearIsometry o.rightAngleRotationAux₂ (-o.rightAngleRotationAux₁)
    (by ext; simp [rightAngleRotationAux₂]) (by ext; simp [rightAngleRotationAux₂])
local notation "J" => o.rightAngleRotation
@[simp]
theorem inner_rightAngleRotation_left (x y : E) : ⟪J x, y⟫ = ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_left x y
@[simp]
theorem inner_rightAngleRotation_right (x y : E) : ⟪x, J y⟫ = -ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_right x y
@[simp]
theorem rightAngleRotation_rightAngleRotation (x : E) : J (J x) = -x := by
  rw [rightAngleRotation]
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x
@[simp]
theorem rightAngleRotation_symm :
    LinearIsometryEquiv.symm J = LinearIsometryEquiv.trans J (LinearIsometryEquiv.neg ℝ) := by
  rw [rightAngleRotation]
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl
theorem inner_rightAngleRotation_self (x : E) : ⟪J x, x⟫ = 0 := by simp
theorem inner_rightAngleRotation_swap (x y : E) : ⟪x, J y⟫ = -⟪J x, y⟫ := by simp
theorem inner_rightAngleRotation_swap' (x y : E) : ⟪J x, y⟫ = -⟪x, J y⟫ := by
  simp [o.inner_rightAngleRotation_swap x y]
theorem inner_comp_rightAngleRotation (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
  LinearIsometryEquiv.inner_map_map J x y
@[simp]
theorem areaForm_rightAngleRotation_left (x y : E) : ω (J x) y = -⟪x, y⟫ := by
  rw [← o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_right, neg_neg]
@[simp]
theorem areaForm_rightAngleRotation_right (x y : E) : ω x (J y) = ⟪x, y⟫ := by
  rw [← o.inner_rightAngleRotation_left, o.inner_comp_rightAngleRotation]
theorem areaForm_comp_rightAngleRotation (x y : E) : ω (J x) (J y) = ω x y := by simp
@[simp]
theorem rightAngleRotation_trans_rightAngleRotation :
    LinearIsometryEquiv.trans J J = LinearIsometryEquiv.neg ℝ := by ext; simp
theorem rightAngleRotation_neg_orientation (x : E) :
    (-o).rightAngleRotation x = -o.rightAngleRotation x := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_rightAngleRotation_left]
  simp
@[simp]
theorem rightAngleRotation_trans_neg_orientation :
    (-o).rightAngleRotation = o.rightAngleRotation.trans (LinearIsometryEquiv.neg ℝ) :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_neg_orientation
theorem rightAngleRotation_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation x =
      φ (o.rightAngleRotation (φ.symm x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_rightAngleRotation_left]
  trans ⟪J (φ.symm x), φ.symm y⟫
  · simp [o.areaForm_map]
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  · rw [φ.inner_map_map]
  · simp
theorem linearIsometryEquiv_comp_rightAngleRotation (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : E) : φ (J x) = J (φ x) := by
  convert (o.rightAngleRotation_map φ (φ x)).symm
  · simp
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]
theorem rightAngleRotation_map' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation =
      (φ.symm.trans o.rightAngleRotation).trans φ :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_map φ
theorem linearIsometryEquiv_comp_rightAngleRotation' (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) :
    LinearIsometryEquiv.trans J φ = φ.trans J :=
  LinearIsometryEquiv.ext <| o.linearIsometryEquiv_comp_rightAngleRotation φ hφ
def basisRightAngleRotation (x : E) (hx : x ≠ 0) : Basis (Fin 2) ℝ E :=
  @basisOfLinearIndependentOfCardEqFinrank ℝ _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all))
    (@Fact.out (finrank ℝ E = 2)).symm
@[simp]
theorem coe_basisRightAngleRotation (x : E) (hx : x ≠ 0) :
    ⇑(o.basisRightAngleRotation x hx) = ![x, J x] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _
theorem inner_mul_inner_add_areaForm_mul_areaForm' (a x : E) :
    ⟪a, x⟫ • innerₛₗ ℝ a + ω a x • ω a = ‖a‖ ^ 2 • innerₛₗ ℝ x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, id_eq, coe_basisRightAngleRotation, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.cons_val_zero, LinearMap.add_apply, LinearMap.smul_apply, innerₛₗ_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul, areaForm_apply_self, mul_zero, add_zero,
      real_inner_comm]
    ring
  · simp only [Fin.mk_one, Fin.isValue, id_eq, coe_basisRightAngleRotation, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.cons_val_one, Matrix.head_cons, LinearMap.add_apply,
      LinearMap.smul_apply, innerₛₗ_apply, inner_rightAngleRotation_right, areaForm_apply_self,
      neg_zero, smul_eq_mul, mul_zero, areaForm_rightAngleRotation_right,
      real_inner_self_eq_norm_sq, zero_add, mul_neg]
    rw [o.areaForm_swap]
    ring
theorem inner_mul_inner_add_areaForm_mul_areaForm (a x y : E) :
    ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫ :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)
theorem inner_sq_add_areaForm_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b
theorem inner_mul_areaForm_sub' (a x : E) : ⟪a, x⟫ • ω a - ω a x • innerₛₗ ℝ a = ‖a‖ ^ 2 • ω x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp only [o.areaForm_swap a x, neg_smul, sub_neg_eq_add, Fin.zero_eta, Fin.isValue, id_eq,
      coe_basisRightAngleRotation, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero,
      LinearMap.add_apply, LinearMap.smul_apply, areaForm_apply_self, smul_eq_mul, mul_zero,
      innerₛₗ_apply, real_inner_self_eq_norm_sq, zero_add]
    ring
  · simp only [Fin.mk_one, Fin.isValue, id_eq, coe_basisRightAngleRotation, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.cons_val_one, Matrix.head_cons, LinearMap.sub_apply,
      LinearMap.smul_apply, areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq,
      smul_eq_mul, innerₛₗ_apply, inner_rightAngleRotation_right, areaForm_apply_self, neg_zero,
      mul_zero, sub_zero, real_inner_comm]
    ring
theorem inner_mul_areaForm_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_areaForm_sub' a x)
theorem nonneg_inner_and_areaForm_eq_zero_iff_sameRay (x y : E) :
    0 ≤ ⟪x, y⟫ ∧ ω x y = 0 ↔ SameRay ℝ x y := by
  by_cases hx : x = 0
  · simp [hx]
  constructor
  · let a : ℝ := (o.basisRightAngleRotation x hx).repr y 0
    let b : ℝ := (o.basisRightAngleRotation x hx).repr y 1
    suffices ↑0 ≤ a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 → SameRay ℝ x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotation x hx).sum_repr y]
      simp only [Fin.sum_univ_succ, coe_basisRightAngleRotation, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one', Finset.univ_eq_empty, Finset.sum_empty, areaForm_apply_self,
        map_smul, map_add, real_inner_smul_right, inner_add_right, Matrix.cons_val_one,
        Matrix.head_cons, Algebra.id.smul_eq_mul, areaForm_rightAngleRotation_right,
        mul_zero, add_zero, zero_add, neg_zero, inner_rightAngleRotation_right,
        real_inner_self_eq_norm_sq, zero_smul, one_smul]
      exact this
    rintro ⟨ha, hb⟩
    have hx' : 0 < ‖x‖ := by simpa using hx
    have ha' : 0 ≤ a := nonneg_of_mul_nonneg_left ha (by positivity)
    have hb' : b = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero 2 hx'.ne') hb
    exact (SameRay.sameRay_nonneg_smul_right x ha').add_right <| by simp [hb']
  · intro h
    obtain ⟨r, hr, rfl⟩ := h.exists_nonneg_left hx
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, LinearMap.map_smulₛₗ,
      areaForm_apply_self, Algebra.id.smul_eq_mul, mul_zero, eq_self_iff_true, and_true]
    positivity
def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.llcomp ℝ E ℝ ℂ Complex.ofRealCLM ∘ₗ innerₛₗ ℝ +
    LinearMap.llcomp ℝ E ℝ ℂ ((LinearMap.lsmul ℝ ℂ).flip Complex.I) ∘ₗ ω
theorem kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • Complex.I :=
  rfl
theorem kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) := by
  simp only [kahler_apply_apply]
  rw [real_inner_comm, areaForm_swap]
  simp [Complex.conj_ofReal]
@[simp]
theorem kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 := by
  simp [kahler_apply_apply, real_inner_self_eq_norm_sq]
@[simp]
theorem kahler_rightAngleRotation_left (x y : E) :
    o.kahler (J x) y = -Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq
@[simp]
theorem kahler_rightAngleRotation_right (x y : E) :
    o.kahler x (J y) = Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq
theorem kahler_comp_rightAngleRotation (x y : E) : o.kahler (J x) (J y) = o.kahler x y := by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  linear_combination -o.kahler x y * Complex.I_sq
theorem kahler_comp_rightAngleRotation' (x y : E) :
    -(Complex.I * (Complex.I * o.kahler x y)) = o.kahler x y := by
  linear_combination -o.kahler x y * Complex.I_sq
@[simp]
theorem kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) := by
  simp [kahler_apply_apply, Complex.conj_ofReal]
theorem kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y := by
  trans ((‖a‖ ^ 2 :) : ℂ) * o.kahler x y
  · apply Complex.ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      linear_combination o.inner_mul_inner_add_areaForm_mul_areaForm a x y
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      linear_combination o.inner_mul_areaForm_sub a x y
  · norm_cast
theorem normSq_kahler (x y : E) : Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y
theorem abs_kahler (x y : E) : Complex.abs (o.kahler x y) = ‖x‖ * ‖y‖ := by
  rw [← sq_eq_sq₀, Complex.sq_abs]
  · linear_combination o.normSq_kahler x y
  · positivity
  · positivity
theorem norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by simpa using o.abs_kahler x y
theorem eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 := by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  cases' eq_zero_or_eq_zero_of_mul_eq_zero this with h h
  · left
    simpa using h
  · right
    simpa using h
theorem kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 := by
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, ?_⟩
  rintro (rfl | rfl) <;> simp
theorem kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 := by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto
theorem kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  refine ⟨?_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp
theorem kahler_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) := by
  simp [kahler_apply_apply, areaForm_map]
theorem kahler_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.kahler (φ x) (φ y) = o.kahler x y := by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]
end Orientation
namespace Complex
attribute [local instance] Complex.finrank_real_complex_fact
@[simp]
protected theorem areaForm (w z : ℂ) : Complex.orientation.areaForm w z = (conj w * z).im := by
  let o := Complex.orientation
  simp only [o.areaForm_to_volumeForm, o.volumeForm_robust Complex.orthonormalBasisOneI rfl,
    Basis.det_apply, Matrix.det_fin_two, Basis.toMatrix_apply, toBasis_orthonormalBasisOneI,
    Matrix.cons_val_zero, coe_basisOneI_repr, Matrix.cons_val_one, Matrix.head_cons, mul_im,
    conj_re, conj_im]
  ring
@[simp]
protected theorem rightAngleRotation (z : ℂ) :
    Complex.orientation.rightAngleRotation z = I * z := by
  apply ext_inner_right ℝ
  intro w
  rw [Orientation.inner_rightAngleRotation_left]
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring
@[simp]
protected theorem kahler (w z : ℂ) : Complex.orientation.kahler w z = conj w * z := by
  rw [Orientation.kahler_apply_apply]
  apply Complex.ext <;> simp
end Complex
namespace Orientation
local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation
open Complex
theorem areaForm_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    ω x y = (conj (f x) * f y).im := by
  rw [← Complex.areaForm, ← hf, areaForm_map (hF := _)]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]
theorem rightAngleRotation_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : E) :
    f (J x) = I * f x := by
  rw [← Complex.rightAngleRotation, ← hf, rightAngleRotation_map (hF := _),
    LinearIsometryEquiv.symm_apply_apply]
theorem kahler_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    o.kahler x y = conj (f x) * f y := by
  rw [← Complex.kahler, ← hf, kahler_map (hF := _)]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]
end Orientation