import Mathlib.Data.Matrix.Basic
assert_not_exists Matrix.trace
variable {l m n : Type*}
variable {R α : Type*}
namespace Matrix
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]
section Zero
variable [Zero α]
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α :=
  of <| fun i' j' => if i = i' ∧ j = j' then a else 0
theorem stdBasisMatrix_eq_of_single_single (i : m) (j : n) (a : α) :
    stdBasisMatrix i j a = Matrix.of (Pi.single i (Pi.single j a)) := by
  ext a b
  unfold stdBasisMatrix
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]
@[simp]
theorem smul_stdBasisMatrix [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) :
    r • stdBasisMatrix i j a = stdBasisMatrix i j (r • a) := by
  unfold stdBasisMatrix
  ext
  simp [smul_ite]
@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 := by
  unfold stdBasisMatrix
  ext
  simp
end Zero
theorem stdBasisMatrix_add [AddZeroClass α] (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b := by
  ext
  simp only [stdBasisMatrix, of_apply]
  split_ifs with h <;> simp [h]
theorem mulVec_stdBasisMatrix [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : n) (j : m) (c : α) (x : m → α) :
    mulVec (stdBasisMatrix i j c) x = Function.update (0 : n → α) i (c * x j) := by
  ext i'
  simp [stdBasisMatrix, mulVec, dotProduct]
  rcases eq_or_ne i i' with rfl|h
  · simp
  simp [h, h.symm]
theorem matrix_eq_sum_stdBasisMatrix [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, stdBasisMatrix i j (x i j) := by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [stdBasisMatrix, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk.inj_iff]
@[deprecated (since := "2024-08-11")] alias matrix_eq_sum_std_basis := matrix_eq_sum_stdBasisMatrix
theorem stdBasisMatrix_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) :
    stdBasisMatrix i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  ext i' j'
  simp [-mul_ite, stdBasisMatrix, vecMulVec, ite_and, Pi.single_apply, eq_comm]
@[deprecated stdBasisMatrix_eq_single_vecMulVec_single (since := "2024-08-11")]
theorem std_basis_eq_basis_mul_basis [MulZeroOneClass α] (i : m) (j : n) :
    stdBasisMatrix i j (1 : α) =
      vecMulVec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 := by
  rw [stdBasisMatrix_eq_single_vecMulVec_single]
  congr! with i <;> simp only [Pi.single_apply, eq_comm]
@[elab_as_elim]
protected theorem induction_on'
    [AddCommMonoid α] [Finite m] [Finite n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M := by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_stdBasisMatrix M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis
@[elab_as_elim]
protected theorem induction_on
    [AddCommMonoid α] [Finite m] [Finite n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (stdBasisMatrix i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis
namespace StdBasisMatrix
section
variable [Zero α] (i : m) (j : n) (c : α) (i' : m) (j' : n)
@[simp]
theorem apply_same : stdBasisMatrix i j c i j = c :=
  if_pos (And.intro rfl rfl)
@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 := by
  simp only [stdBasisMatrix, and_imp, ite_eq_right_iff, of_apply]
  tauto
@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]
@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]
end
section
variable [Zero α] (i j : n) (c : α)
@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)
@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]
end
section mul
variable [Fintype n] [NonUnitalNonAssocSemiring α] (i j : n) (c : α)
@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) :
    (stdBasisMatrix i j c * M) i b = c * M j b := by simp [mul_apply, stdBasisMatrix]
@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) :
    (M * stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, stdBasisMatrix, mul_comm]
@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) :
    (stdBasisMatrix i j c * M) a b = 0 := by simp [mul_apply, h.symm]
@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) :
    (M * stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]
@[simp]
theorem mul_same (k : n) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix j k d = stdBasisMatrix i k (c * d) := by
  ext a b
  simp only [mul_apply, stdBasisMatrix, boole_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]
@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix k l d = 0 := by
  ext a b
  simp only [mul_apply, boole_mul, stdBasisMatrix, of_apply]
  by_cases h₁ : i = a
  · simp only [h₁, true_and, mul_ite, ite_mul, zero_mul, mul_zero, ← ite_and, zero_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    apply if_neg
    rintro ⟨⟨rfl, rfl⟩, h⟩
    contradiction
  · simp only [h₁, false_and, ite_false, mul_ite, zero_mul, mul_zero, ite_self,
      Finset.sum_const_zero, zero_apply]
end mul
end StdBasisMatrix
section Commute
variable [Fintype n] [Semiring α]
theorem row_eq_zero_of_commute_stdBasisMatrix {i j k : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) (hkj : k ≠ j) : M j k = 0 := by
  have := ext_iff.mpr hM i k
  aesop
theorem col_eq_zero_of_commute_stdBasisMatrix {i j k : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) (hki : k ≠ i) : M k i = 0 := by
  have := ext_iff.mpr hM k j
  aesop
theorem diag_eq_of_commute_stdBasisMatrix {i j : n} {M : Matrix n n α}
    (hM : Commute (stdBasisMatrix i j 1) M) : M i i = M j j := by
  have := ext_iff.mpr hM i j
  aesop
theorem mem_range_scalar_of_commute_stdBasisMatrix {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (stdBasisMatrix i j 1) M) :
    M ∈ Set.range (Matrix.scalar n) := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_stdBasisMatrix (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_stdBasisMatrix (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_stdBasisMatrix (hM hij) hkl.symm]
theorem mem_range_scalar_iff_commute_stdBasisMatrix {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), i ≠ j → Commute (stdBasisMatrix i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_stdBasisMatrix⟩
  rw [scalar_commute_iff]
  simp
theorem mem_range_scalar_iff_commute_stdBasisMatrix' {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), Commute (stdBasisMatrix i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
    fun hM => mem_range_scalar_iff_commute_stdBasisMatrix.mpr <| fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp
end Commute
end Matrix