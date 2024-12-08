import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.SetTheory.Cardinal.Basic
assert_not_exists Module
assert_not_exists Field
open Cardinal
theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ