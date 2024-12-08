import Mathlib.Algebra.Group.Nat.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
open Multiplicative
namespace Nat
lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm
end Nat