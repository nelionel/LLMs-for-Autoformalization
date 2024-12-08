import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
namespace Matrix
universe u u' v
variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}
open Matrix Equiv Equiv.Perm Finset
section Invertible
variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟ A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, invOf_mul_self, one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc, adjugate_mul, smul_smul, invOf_mul_self, one_smul]
theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟ A = ⅟ A.det • A.adjugate := by
  letI := invertibleOfDetInvertible A
  convert (rfl : ⅟ A = _)
def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]
def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟ A) (invOf_mul_self _)
theorem det_invOf [Invertible A] [Invertible A.det] : (⅟ A).det = ⅟ A.det := by
  letI := detInvertibleOfInvertible A
  convert (rfl : _ = ⅟ A.det)
@[simps]
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
variable {A B}
theorem mul_eq_one_comm : A * B = 1 ↔ B * A = 1 :=
  suffices ∀ A B : Matrix n n α, A * B = 1 → B * A = 1 from ⟨this A B, this B A⟩
  fun A B h => by
  letI : Invertible B.det := detInvertibleOfLeftInverse _ _ h
  letI : Invertible B := invertibleOfDetInvertible B
  calc
    B * A = B * A * (B * ⅟ B) := by rw [mul_invOf_self, Matrix.mul_one]
    _ = B * (A * B * ⅟ B) := by simp only [Matrix.mul_assoc]
    _ = B * ⅟ B := by rw [h, Matrix.one_mul]
    _ = 1 := mul_invOf_self B
variable (A B)
def invertibleOfLeftInverse (h : B * A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩
def invertibleOfRightInverse (h : A * B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)
theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]
@[simp]
theorem isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp A.isUnit
theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)
variable {A B}
theorem isUnit_of_left_inverse (h : B * A = 1) : IsUnit A :=
  ⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩
theorem exists_left_inverse_iff_isUnit : (∃ B, B * A = 1) ↔ IsUnit A :=
  ⟨fun ⟨_, h⟩ ↦ isUnit_of_left_inverse h, fun h ↦ have := h.invertible; ⟨⅟A, invOf_mul_self' A⟩⟩
theorem isUnit_of_right_inverse (h : A * B = 1) : IsUnit A :=
  ⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩
theorem exists_right_inverse_iff_isUnit : (∃ B, A * B = 1) ↔ IsUnit A :=
  ⟨fun ⟨_, h⟩ ↦ isUnit_of_right_inverse h, fun h ↦ have := h.invertible; ⟨⅟A, mul_invOf_self' A⟩⟩
theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)
theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)
theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det ≠ 0 :=
  (isUnit_det_of_left_inverse h).ne_zero
theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det ≠ 0 :=
  (isUnit_det_of_right_inverse h).ne_zero
end Invertible
section
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α]
theorem mul_eq_one_comm_of_equiv {A : Matrix m n α} {B : Matrix n m α} (e : m ≃ n) :
    A * B = 1 ↔ B * A = 1 := by
  refine (reindex e e).injective.eq_iff.symm.trans ?_
  rw [reindex_apply, reindex_apply, submatrix_one_equiv, ← submatrix_mul_equiv _ _ _ (.refl _),
    mul_eq_one_comm, submatrix_mul_equiv, coe_refl, submatrix_id_id]
end
section Inv
variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)
theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h
noncomputable instance inv : Inv (Matrix n n α) :=
  ⟨fun A => Ring.inverse A.det • A.adjugate⟩
theorem inv_def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl
theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]
theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]
@[simp]
theorem invOf_eq_nonsing_inv [Invertible A] : ⅟ A = A⁻¹ := by
  letI := detInvertibleOfInvertible A
  rw [inv_def, Ring.inverse_invertible, invOf_eq]
@[simp, norm_cast]
theorem coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n α) := by
  letI := A.invertible
  rw [← invOf_eq_nonsing_inv, invOf_units]
theorem nonsing_inv_eq_ring_inverse : A⁻¹ = Ring.inverse A := by
  by_cases h_det : IsUnit A.det
  · cases (A.isUnit_iff_isUnit_det.mpr h_det).nonempty_invertible
    rw [← invOf_eq_nonsing_inv, Ring.inverse_invertible]
  · have h := mt A.isUnit_iff_isUnit_det.mp h_det
    rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit A h_det]
theorem transpose_nonsing_inv : A⁻¹ᵀ = Aᵀ⁻¹ := by
  rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]
theorem conjTranspose_nonsing_inv [StarRing α] : A⁻¹ᴴ = Aᴴ⁻¹ := by
  rw [inv_def, inv_def, conjTranspose_smul, det_conjTranspose, adjugate_conjTranspose,
    Ring.inverse_star]
@[simp]
theorem mul_nonsing_inv (h : IsUnit A.det) : A * A⁻¹ = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv, mul_invOf_self]
@[simp]
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1 := by
  cases (A.isUnit_iff_isUnit_det.mpr h).nonempty_invertible
  rw [← invOf_eq_nonsing_inv, invOf_mul_self]
instance [Invertible A] : Invertible A⁻¹ := by
  rw [← invOf_eq_nonsing_inv]
  infer_instance
@[simp]
theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
  simp only [← invOf_eq_nonsing_inv, invOf_invOf]
@[simp]
theorem mul_nonsing_inv_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B := by
  simp [Matrix.mul_assoc, mul_nonsing_inv A h]
@[simp]
theorem mul_nonsing_inv_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B := by
  simp [← Matrix.mul_assoc, mul_nonsing_inv A h]
@[simp]
theorem nonsing_inv_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B := by
  simp [Matrix.mul_assoc, nonsing_inv_mul A h]
@[simp]
theorem nonsing_inv_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) : A⁻¹ * (A * B) = B := by
  simp [← Matrix.mul_assoc, nonsing_inv_mul A h]
@[simp]
theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 :=
  mul_nonsing_inv A (isUnit_det_of_invertible A)
@[simp]
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 :=
  nonsing_inv_mul A (isUnit_det_of_invertible A)
@[simp]
theorem mul_inv_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A * A⁻¹ = B :=
  mul_nonsing_inv_cancel_right A B (isUnit_det_of_invertible A)
@[simp]
theorem mul_inv_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A * (A⁻¹ * B) = B :=
  mul_nonsing_inv_cancel_left A B (isUnit_det_of_invertible A)
@[simp]
theorem inv_mul_cancel_right_of_invertible (B : Matrix m n α) [Invertible A] : B * A⁻¹ * A = B :=
  nonsing_inv_mul_cancel_right A B (isUnit_det_of_invertible A)
@[simp]
theorem inv_mul_cancel_left_of_invertible (B : Matrix n m α) [Invertible A] : A⁻¹ * (A * B) = B :=
  nonsing_inv_mul_cancel_left A B (isUnit_det_of_invertible A)
theorem inv_mul_eq_iff_eq_mul_of_invertible (A B C : Matrix n n α) [Invertible A] :
    A⁻¹ * B = C ↔ B = A * C :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, inv_mul_cancel_left_of_invertible]⟩
theorem mul_inv_eq_iff_eq_mul_of_invertible (A B C : Matrix n n α) [Invertible A] :
    B * A⁻¹ = C ↔ B = C * A :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, mul_inv_cancel_right_of_invertible]⟩
lemma inv_mulVec_eq_vec {A : Matrix n n α} [Invertible A]
    {u v : n → α} (hM : u = A.mulVec v) : A⁻¹.mulVec u = v := by
  rw [hM, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
lemma mul_right_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ h => by simpa only [inv_mul_cancel_left_of_invertible] using congr_arg (A⁻¹ * ·) h
lemma mul_left_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun a x hax => by simpa only [mul_inv_cancel_right_of_invertible] using congr_arg (· * A⁻¹) hax
lemma mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = A * y ↔ x = y :=
  (mul_right_injective_of_invertible A).eq_iff
lemma mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y * A ↔ x = y :=
  (mul_left_injective_of_invertible A).eq_iff
end Inv
section InjectiveMul
variable [Fintype n] [Fintype m] [DecidableEq m] [CommRing α]
lemma mul_left_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix l m α => x * A) := fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g
lemma mul_right_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix m l α => B * x) :=
  fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g
end InjectiveMul
section vecMul
section Semiring
variable {R : Type*} [Semiring R]
theorem vecMul_surjective_iff_exists_left_inverse
    [DecidableEq n] [Fintype m] [Finite n] {A : Matrix m n R} :
    Function.Surjective A.vecMul ↔ ∃ B : Matrix n m R, B * A = 1 := by
  cases nonempty_fintype n
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul, one_eq_pi_single, ← hrows]
  rfl
theorem mulVec_surjective_iff_exists_right_inverse
    [DecidableEq m] [Finite m] [Fintype n] {A : Matrix m n R} :
    Function.Surjective A.mulVec ↔ ∃ B : Matrix n m R, A * B = 1 := by
  cases nonempty_fintype m
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j ↦ ?_⟩
  rw [one_eq_pi_single, Pi.single_comm, ← hcols j]
  rfl
end Semiring
variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]
theorem vecMul_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [vecMul_surjective_iff_exists_left_inverse, exists_left_inverse_iff_isUnit]
theorem mulVec_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.mulVec ↔ IsUnit A := by
  rw [mulVec_surjective_iff_exists_right_inverse, exists_right_inverse_iff_isUnit]
theorem vecMul_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.vecMul ↔ IsUnit A := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  change Function.Injective A.vecMulLinear
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  replace h := h.invertible
  simpa using congr_arg A⁻¹.vecMulLinear hc
theorem mulVec_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.mulVec ↔ IsUnit A := by
  rw [← isUnit_transpose, ← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]
theorem linearIndependent_rows_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K (fun i ↦ A i) ↔ IsUnit A := by
  rw [← transpose_transpose A, ← mulVec_injective_iff, ← coe_mulVecLin, mulVecLin_transpose,
    transpose_transpose, ← vecMul_injective_iff_isUnit, coe_vecMulLinear]
theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K (fun i ↦ Aᵀ i) ↔ IsUnit A := by
  rw [← transpose_transpose A, isUnit_transpose, linearIndependent_rows_iff_isUnit,
    transpose_transpose]
theorem vecMul_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.vecMul :=
  vecMul_surjective_iff_isUnit.2 <| isUnit_of_invertible A
theorem mulVec_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.mulVec :=
  mulVec_surjective_iff_isUnit.2 <| isUnit_of_invertible A
theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul :=
  vecMul_injective_iff_isUnit.2 <| isUnit_of_invertible A
theorem mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.mulVec :=
  mulVec_injective_iff_isUnit.2 <| isUnit_of_invertible A
theorem linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K (fun i ↦ A i) :=
  linearIndependent_rows_iff_isUnit.2 <| isUnit_of_invertible A
theorem linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K (fun i ↦ Aᵀ i) :=
  linearIndependent_cols_iff_isUnit.2 <| isUnit_of_invertible A
end vecMul
variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)
theorem nonsing_inv_cancel_or_zero : A⁻¹ * A = 1 ∧ A * A⁻¹ = 1 ∨ A⁻¹ = 0 := by
  by_cases h : IsUnit A.det
  · exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)
theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1 := by
  rw [← det_mul, A.nonsing_inv_mul h, det_one]
@[simp]
theorem det_nonsing_inv : A⁻¹.det = Ring.inverse A.det := by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    letI := invertibleOfDetInvertible A
    rw [Ring.inverse_invertible, ← invOf_eq_nonsing_inv, det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero ‹_›]
theorem isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  isUnit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)
@[simp]
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc
    A⁻¹⁻¹ = 1 * A⁻¹⁻¹ := by rw [Matrix.one_mul]
    _ = A * A⁻¹ * A⁻¹⁻¹ := by rw [A.mul_nonsing_inv h]
    _ = A := by
      rw [Matrix.mul_assoc, A⁻¹.mul_nonsing_inv (A.isUnit_nonsing_inv_det h), Matrix.mul_one]
theorem isUnit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det := by
  rw [Matrix.det_nonsing_inv, isUnit_ring_inverse]
@[simp]
theorem isUnit_nonsing_inv_iff {A : Matrix n n α} : IsUnit A⁻¹ ↔ IsUnit A := by
  simp_rw [isUnit_iff_isUnit_det, isUnit_nonsing_inv_det_iff]
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)
theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  rfl
variable {A} {B}
theorem inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B :=
  letI := invertibleOfLeftInverse _ _ h
  invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h
theorem inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)
section InvEqInv
variable {C : Matrix n n α}
theorem left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_left_inv h, ← inv_eq_left_inv g]
theorem right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_right_inv g]
theorem right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C := by
  rw [← inv_eq_right_inv h, ← inv_eq_left_inv g]
theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B := by
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') ?_
  rw [h]
  refine mul_nonsing_inv _ ?_
  rwa [← isUnit_nonsing_inv_det_iff, ← h, isUnit_nonsing_inv_det_iff]
end InvEqInv
variable (A)
@[simp]
theorem inv_zero : (0 : Matrix n n α)⁻¹ = 0 := by
  cases' subsingleton_or_nontrivial α with ht ht
  · simp [eq_iff_true_of_subsingleton]
  rcases (Fintype.card n).zero_le.eq_or_lt with hc | hc
  · rw [eq_comm, Fintype.card_eq_zero_iff] at hc
    haveI := hc
    ext i
    exact (IsEmpty.false i).elim
  · have hn : Nonempty n := Fintype.card_pos_iff.mp hc
    refine nonsing_inv_apply_not_isUnit _ ?_
    simp [hn]
noncomputable instance : InvOneClass (Matrix n n α) :=
  { Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }
theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟ k • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
theorem inv_smul' (k : αˣ) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv (by simp [h, smul_smul])
theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : (adjugate A)⁻¹ = h.unit⁻¹ • A := by
  refine inv_eq_left_inv ?_
  rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.val_inv_mul, one_smul]
section Diagonal
def diagonalInvertible {α} [NonAssocSemiring α] (v : n → α) [Invertible v] :
    Invertible (diagonal v) :=
  Invertible.map (diagonalRingHom n α) v
theorem invOf_diagonal_eq {α} [Semiring α] (v : n → α) [Invertible v] [Invertible (diagonal v)] :
    ⅟ (diagonal v) = diagonal (⅟ v) := by
  letI := diagonalInvertible v
  convert (rfl : ⅟ (diagonal v) = _)
def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟ (diagonal v))
  invOf_mul_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      letI : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_left_comm, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
@[simps]
def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
@[simp]
theorem isUnit_diagonal {v : n → α} : IsUnit (diagonal v) ↔ IsUnit v := by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]
theorem inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal (Ring.inverse v) := by
  rw [nonsing_inv_eq_ring_inverse]
  by_cases h : IsUnit v
  · have := isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible, Ring.inverse_invertible, invOf_diagonal_eq]
  · have := isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h, Pi.zero_def, diagonal_zero, Ring.inverse_non_unit _ this]
end Diagonal
@[simp]
theorem inv_subsingleton [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix m m α) :
    A⁻¹ = diagonal fun i => Ring.inverse (A i i) := by
  rw [inv_def, adjugate_subsingleton, smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _
section Woodbury
variable [Fintype m] [DecidableEq m]
variable (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
theorem add_mul_mul_inv_eq_sub (hA : IsUnit A) (hC : IsUnit C) (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨_⟩ := hC.nonempty_invertible
  obtain ⟨iAC⟩ := hAC.nonempty_invertible
  simp only [← invOf_eq_nonsing_inv] at iAC
  letI := invertibleAddMulMul A U C V
  simp only [← invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul
end Woodbury
@[simp]
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ := by
  by_cases h : IsUnit A.det
  · rw [nonsing_inv_nonsing_inv _ h]
  · simp [nonsing_inv_apply_not_isUnit _ h]
theorem inv_add_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ + B⁻¹ = A⁻¹ * (A + B) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ring_inverse] using Ring.inverse_add_inverse h
theorem inv_sub_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  simpa only [nonsing_inv_eq_ring_inverse] using Ring.inverse_sub_inverse h
theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]
theorem list_prod_inv_reverse : ∀ l : List (Matrix n n α), l.prod⁻¹ = (l.reverse.map Inv.inv).prod
  | [] => by rw [List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | A::Xs => by
    rw [List.reverse_cons', List.map_concat, List.prod_concat, List.prod_cons,
      mul_inv_rev, list_prod_inv_reverse Xs]
@[simp]
theorem det_smul_inv_mulVec_eq_cramer (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • A⁻¹ *ᵥ b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, A.nonsing_inv_apply h, ← smul_mulVec_assoc, smul_smul,
    h.mul_val_inv, one_smul]
@[simp]
theorem det_smul_inv_vecMul_eq_cramer_transpose (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • b ᵥ* A⁻¹ = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose, vecMul_transpose, transpose_nonsing_inv, ← det_transpose,
    Aᵀ.det_smul_inv_mulVec_eq_cramer _ (isUnit_det_transpose A h)]
section Submatrix
variable [Fintype m]
variable [DecidableEq m]
def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
  invertibleOfRightInverse _ ((⅟ A).submatrix e₂ e₁) <| by
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
  invertibleOfRightInverse _ ((⅟ (A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) <| by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    rw [congr_arg₂ (· * ·) this rfl]
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]
theorem invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
    [Invertible (A.submatrix e₁ e₂)] : ⅟ (A.submatrix e₁ e₂) = (⅟ A).submatrix e₂ e₁ := by
  letI := submatrixEquivInvertible A e₁ e₂
  convert (rfl : ⅟ (A.submatrix e₁ e₂) = _)
@[simps]
def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
@[simp]
theorem isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) :
    IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]
@[simp]
theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁ := by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    letI := submatrixEquivInvertible A e₁ e₂
    rw [← invOf_eq_nonsing_inv, ← invOf_eq_nonsing_inv, invOf_submatrix_equiv_eq A]
  · have := (isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [nonsing_inv_eq_ring_inverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]
theorem inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) : (reindex e₁ e₂ A)⁻¹ = reindex e₂ e₁ A⁻¹ :=
  inv_submatrix_equiv A e₁.symm e₂.symm
end Submatrix
section Det
variable [Fintype m] [DecidableEq m]
theorem det_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M * N * M⁻¹) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj]
theorem det_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    det (M⁻¹ * N * M) = det N := by rw [← h.unit_spec, ← coe_units_inv, det_units_conj']
end Det
section trace
variable [Fintype m] [DecidableEq m]
theorem trace_conj {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M * N * M⁻¹) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj]
theorem trace_conj' {M : Matrix m m α} (h : IsUnit M) (N : Matrix m m α) :
    trace (M⁻¹ * N * M) = trace N := by rw [← h.unit_spec, ← coe_units_inv, trace_units_conj']
end trace
end Matrix