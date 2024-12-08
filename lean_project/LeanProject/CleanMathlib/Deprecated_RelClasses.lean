import Mathlib.Deprecated.AlgebraClasses
import Mathlib.Order.RelClasses
set_option linter.deprecated false
universe u v
variable {α : Type u}
open Function
@[deprecated "No deprecation message was provided." (since := "2024-07-30")]
theorem IsTotalPreorder.swap (r) [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with }
@[deprecated "No deprecation message was provided." (since := "2024-08-22")]
instance [LinearOrder α] : IsTotalPreorder α (· ≤ ·) where
@[deprecated "No deprecation message was provided." (since := "2024-08-22")]
instance [LinearOrder α] : IsTotalPreorder α (· ≥ ·) where
@[deprecated "No deprecation message was provided." (since := "2024-07-30")]
instance [LinearOrder α] : IsIncompTrans α (· < ·) := by infer_instance