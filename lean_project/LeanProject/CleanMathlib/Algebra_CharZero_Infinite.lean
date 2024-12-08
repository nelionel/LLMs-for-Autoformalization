import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Fintype.Card
open Set
variable (M : Type*) [AddMonoidWithOne M] [CharZero M]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective Nat.cast Nat.cast_injective