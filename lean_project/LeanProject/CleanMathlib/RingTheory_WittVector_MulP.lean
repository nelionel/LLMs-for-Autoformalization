import Mathlib.RingTheory.WittVector.IsPoly
namespace WittVector
variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]
local notation "𝕎" => WittVector p 
open MvPolynomial
noncomputable section
variable (p)
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![wittMulN n, X]) (wittAdd p k)
variable {p}
theorem mulN_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) :
    (x * n).coeff k = aeval x.coeff (wittMulN p n k) := by
  induction' n with n ih generalizing k
  · simp only [Nat.cast_zero, mul_zero, zero_coeff, wittMulN, Pi.zero_apply, map_zero]
  · rw [wittMulN, Nat.cast_add, Nat.cast_one, mul_add, mul_one, aeval_bind₁, add_coeff]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1 ⟨b, i⟩
    fin_cases b
    · simp [Function.uncurry, Matrix.cons_val_zero, ih]
    · simp [Function.uncurry, Matrix.cons_val_one, Matrix.head_cons, aeval_X]
variable (p)
@[is_poly]
theorem mulN_isPoly (n : ℕ) : IsPoly p fun _ _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩
@[simp]
theorem bind₁_wittMulN_wittPolynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k := by
  induction' n with n ih
  · simp [wittMulN, Nat.cast_zero, zero_mul, bind₁_zero_wittPolynomial]
  · rw [wittMulN, ← bind₁_bind₁, wittAdd, wittStructureInt_prop]
    simp only [map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename]
    simp only [ih, Function.uncurry, Function.comp_def, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
end
end WittVector