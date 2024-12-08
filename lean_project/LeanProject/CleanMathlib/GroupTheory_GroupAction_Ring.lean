import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.SMulWithZero
open scoped Int
variable {α : Type*}
instance NonUnitalNonAssocSemiring.toDistribSMul [NonUnitalNonAssocSemiring α] :
    DistribSMul α α where smul_add := mul_add
instance NonUnitalNonAssocSemiring.nat_smulCommClass [NonUnitalNonAssocSemiring α] :
    SMulCommClass ℕ α α where
  smul_comm n x y := by
    induction n with
    | zero => simp [zero_nsmul]
    | succ n ih => simp_rw [succ_nsmul, smul_eq_mul, mul_add, ← smul_eq_mul, ih]
instance NonUnitalNonAssocSemiring.nat_isScalarTower [NonUnitalNonAssocSemiring α] :
    IsScalarTower ℕ α α where
  smul_assoc n x y := by
    induction n with
    | zero => simp [zero_nsmul]
    | succ n ih => simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]
instance NonUnitalNonAssocRing.int_smulCommClass [NonUnitalNonAssocRing α] :
    SMulCommClass ℤ α α where
  smul_comm n x y :=
    match n with
    | (n : ℕ) => by simp_rw [natCast_zsmul, smul_comm]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, mul_neg, mul_smul_comm]
instance NonUnitalNonAssocRing.int_isScalarTower [NonUnitalNonAssocRing α] :
    IsScalarTower ℤ α α where
  smul_assoc n x y :=
    match n with
    | (n : ℕ) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]