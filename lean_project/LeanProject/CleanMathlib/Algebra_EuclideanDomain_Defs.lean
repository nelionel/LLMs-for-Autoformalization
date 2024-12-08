import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.RelClasses
universe u
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
  protected quotient : R → R → R
  protected quotient_zero : ∀ a, quotient a 0 = 0
  protected remainder : R → R → R
  protected quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
  protected r : R → R → Prop
  r_wellFounded : WellFounded r
  protected remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a
namespace EuclideanDomain
variable {R : Type u} [EuclideanDomain R]
local infixl:50 " ≺ " => EuclideanDomain.r
local instance wellFoundedRelation : WellFoundedRelation R where
  wf := r_wellFounded
instance isWellFounded : IsWellFounded R (· ≺ ·) where
  wf := r_wellFounded
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩
theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _
theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)
theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _
theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _
theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]
theorem mod_lt : ∀ (a) {b : R}, b ≠ 0 → a % b ≺ b :=
  EuclideanDomain.remainder_lt
theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h
@[simp]
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0
theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 :=
  haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h
theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)
@[simp]
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a
section
@[elab_as_elim]
theorem GCD.induction {P : R → R → Prop} (a b : R) (H0 : ∀ x, P 0 x)
    (H1 : ∀ a b, a ≠ 0 → P (b % a) a → P a b) : P a b := by
  classical
  exact if a0 : a = 0 then by
    change P a b
    exact a0.symm ▸ H0 b
  else
    have _ := mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a
end
section GCD
variable [DecidableEq R]
def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a
@[simp]
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl
def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r
@[simp]
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcdAux
  exact if_pos rfl
theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2
def gcdA (x y : R) : R :=
  (xgcd x y).1
def gcdB (x y : R) : R :=
  (xgcd x y).2
@[simp]
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]
@[simp]
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]
theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  rfl
end GCD
section LCM
variable [DecidableEq R]
def lcm (x y : R) : R :=
  x * y / gcd x y
end LCM
end EuclideanDomain