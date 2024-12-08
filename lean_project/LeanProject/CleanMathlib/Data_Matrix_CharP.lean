import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Matrix.Diagonal
open Matrix
variable {n : Type*} {R : Type*} [AddMonoidWithOne R]
instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] :
    CharP (Matrix n n R) p where
  cast_eq_zero_iff' k := by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]