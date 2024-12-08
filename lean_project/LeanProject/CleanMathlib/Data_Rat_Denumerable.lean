import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Logic.Denumerable
assert_not_exists Module
assert_not_exists Field
namespace Rat
open Denumerable
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ
end Rat