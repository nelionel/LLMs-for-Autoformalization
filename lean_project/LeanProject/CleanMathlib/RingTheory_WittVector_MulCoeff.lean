import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.WittVector.Truncated
noncomputable section
namespace WittVector
variable (p : ℕ) [hp : Fact p.Prime]
variable {k : Type*} [CommRing k]
local notation "𝕎" => WittVector p
local notation "𝕄" => MvPolynomial (Fin 2 × ℕ) ℤ
open Finset MvPolynomial
def wittPolyProd (n : ℕ) : 𝕄 :=
  rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ n)
theorem wittPolyProd_vars (n : ℕ) : (wittPolyProd p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [wittPolyProd]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_rename _ _) ?_
    simp [wittPolynomial_vars, image_subset_iff]
def wittPolyProdRemainder (n : ℕ) : 𝕄 :=
  ∑ i ∈ range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)
theorem wittPolyProdRemainder_vars (n : ℕ) :
    (wittPolyProdRemainder p n).vars ⊆ univ ×ˢ range n := by
  rw [wittPolyProdRemainder]
  refine Subset.trans (vars_sum_subset _ _) ?_
  rw [biUnion_subset]
  intro x hx
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_
  · apply Subset.trans (vars_pow _ _)
    have : (p : 𝕄) = C (p : ℤ) := by simp only [Int.cast_natCast, eq_intCast]
    rw [this, vars_C]
    apply empty_subset
  · apply Subset.trans (vars_pow _ _)
    apply Subset.trans (wittMul_vars _ _)
    apply product_subset_product (Subset.refl _)
    simp only [mem_range, range_subset] at hx ⊢
    exact hx
def remainder (n : ℕ) : 𝕄 :=
  (∑ x ∈ range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))) *
   ∑ x ∈ range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))
theorem remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [remainder]
  apply Subset.trans (vars_mul _ _)
  refine union_subset ?_ ?_ <;>
  · refine Subset.trans (vars_sum_subset _ _) ?_
    rw [biUnion_subset]
    intro x hx
    rw [rename_monomial, vars_monomial, Finsupp.mapDomain_single]
    · apply Subset.trans Finsupp.support_single_subset
      simpa using mem_range.mp hx
    · apply pow_ne_zero
      exact mod_cast hp.out.ne_zero
def polyOfInterest (n : ℕ) : 𝕄 :=
  wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1))
theorem mul_polyOfInterest_aux1 (n : ℕ) :
    ∑ i ∈ range (n + 1), (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i) = wittPolyProd p n := by
  simp only [wittPolyProd]
  convert wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  · simp only [wittPolynomial, wittMul]
    rw [map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
      simp only [and_true, Finsupp.single_eq_same, eq_self_iff_true, Ne]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [bind₁_monomial, hsupp, Int.cast_natCast, prod_singleton, eq_intCast,
      Finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, eq_self_iff_true, Int.cast_pow]
  · simp only [map_mul, bind₁_X_right]
theorem mul_polyOfInterest_aux2 (n : ℕ) :
    (p : 𝕄) ^ n * wittMul p n + wittPolyProdRemainder p n = wittPolyProd p n := by
  convert mul_polyOfInterest_aux1 p n
  rw [sum_range_succ, add_comm, Nat.sub_self, pow_zero, pow_one]
  rfl
theorem mul_polyOfInterest_aux3 (p n : ℕ) : wittPolyProd p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    remainder p n := by
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : ℤ) ^ (n + 1)) := by norm_cast
  rw [wittPolyProd, wittPolynomial, map_sum, map_sum]
  conv_lhs =>
    arg 1
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_lhs =>
    arg 2
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  simp only [add_mul, mul_add]
  rw [add_comm _ (remainder p n)]
  simp only [add_assoc]
  apply congrArg (Add.add _)
  ring
theorem mul_polyOfInterest_aux4 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * wittMul p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (remainder p n - wittPolyProdRemainder p (n + 1)) := by
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_polyOfInterest_aux2]
  exact mul_polyOfInterest_aux3 _ _
theorem mul_polyOfInterest_aux5 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * polyOfInterest p n = remainder p n - wittPolyProdRemainder p (n + 1) := by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  rw [mul_polyOfInterest_aux4 p n]
  ring
theorem mul_polyOfInterest_vars (n : ℕ) :
    ((p : 𝕄) ^ (n + 1) * polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [mul_polyOfInterest_aux5]
  apply Subset.trans (vars_sub_subset _)
  refine union_subset ?_ ?_
  · apply remainder_vars
  · apply wittPolyProdRemainder_vars
theorem polyOfInterest_vars_eq (n : ℕ) : (polyOfInterest p n).vars =
    ((p : 𝕄) ^ (n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
      X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
      X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)))).vars := by
  have : (p : 𝕄) ^ (n + 1) = C ((p : ℤ) ^ (n + 1)) := by norm_cast
  rw [polyOfInterest, this, vars_C_mul]
  apply pow_ne_zero
  exact mod_cast hp.out.ne_zero
theorem polyOfInterest_vars (n : ℕ) : (polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars
theorem peval_polyOfInterest (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
    (x * y).coeff (n + 1) + p ^ (n + 1) * x.coeff (n + 1) * y.coeff (n + 1) -
      y.coeff (n + 1) * ∑ i ∈ range (n + 1 + 1), p ^ i * x.coeff i ^ p ^ (n + 1 - i) -
      x.coeff (n + 1) * ∑ i ∈ range (n + 1 + 1), p ^ i * y.coeff i ^ p ^ (n + 1 - i) := by
  simp only [polyOfInterest, peval, map_natCast, Matrix.head_cons, map_pow,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub, add_comm (_ * _), ← sub_sub]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, eval₂_rename, mul_coeff, peval, map_natCast,
    map_add, map_pow, map_mul]
variable [CharP k p]
theorem peval_polyOfInterest' (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  rw [peval_polyOfInterest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [this, Nat.cast_pow, ne_eq, add_eq_zero, and_false, zero_pow, zero_mul, add_zero,
    not_false_eq_true, reduceCtorEq]
  have sum_zero_pow_mul_pow_p (y : 𝕎 k) : ∑ x ∈ range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (n + 1 - x) = y.coeff 0 ^ p ^ (n + 1) := by
    rw [Finset.sum_eq_single_of_mem 0] <;> simp +contextual
  congr <;> apply sum_zero_pow_mul_pow_p
variable (k)
theorem nth_mul_coeff' (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, f (truncateFun (n + 1) x) (truncateFun (n + 1) y) =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  simp only [← peval_polyOfInterest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars k (polyOfInterest_vars p n)
  have : ∀ (a : Multiset (Fin 2)) (b : Multiset ℕ), a ×ˢ b = a.product b := fun a b => rfl
  let f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    apply Function.uncurry ![x, y]
    simp_rw [product_val, this, range_val, Multiset.range_succ] at ha
    let S : Set (Fin 2 × ℕ) := (fun a => a.2 = n ∨ a.2 < n)
    have ha' : a ∈ S := by
      convert ha
      dsimp [S]
      congr!
      simp
    refine ⟨a.fst, ⟨a.snd, ?_⟩⟩
    cases' ha' with ha ha <;> omega
  use f
  intro x y
  dsimp [f, peval]
  rw [← hf₀]
  congr
  ext a
  cases' a with a ha
  cases' a with i m
  fin_cases i <;> rfl 
theorem nth_mul_coeff (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, (x * y).coeff (n + 1) =
      x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
      f (truncateFun (n + 1) x) (truncateFun (n + 1) y) := by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring
variable {k}
def nthRemainder (n : ℕ) : (Fin (n + 1) → k) → (Fin (n + 1) → k) → k :=
  Classical.choose (nth_mul_coeff p k n)
theorem nthRemainder_spec (n : ℕ) (x y : 𝕎 k) : (x * y).coeff (n + 1) =
    x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
    nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  Classical.choose_spec (nth_mul_coeff p k n) _ _
end WittVector