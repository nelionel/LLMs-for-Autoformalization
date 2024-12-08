import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Data.PNat.Basic
variable {M : Type*}
class PNatPowAssoc (M : Type*) [Mul M] [Pow M ℕ+] : Prop where
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x
section Mul
variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]
theorem ppow_add (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x
@[simp]
theorem ppow_one (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x
theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]
theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]
theorem ppow_mul (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  refine PNat.recOn n ?_ fun k hk ↦ ?_
  · rw [ppow_one, mul_one]
  · rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]
theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m
end Mul
instance Pi.instPNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, Mul <| α i] [∀ i, Pow (α i) ℕ+]
    [∀ i, PNatPowAssoc <| α i] : PNatPowAssoc (∀ i, α i) where
  ppow_add _ _ _ := by ext; simp [ppow_add]
  ppow_one _ := by ext; simp
instance Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M] [Mul N] [Pow N ℕ+]
    [PNatPowAssoc N] : PNatPowAssoc (M × N) where
  ppow_add _ _ _ := by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp
theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  refine PNat.recOn n ?_ fun k hk ↦ ?_
  · rw [ppow_one, PNat.one_coe, pow_one]
  · rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]