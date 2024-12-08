import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Sym.Basic
open Mathlib (Vector)
variable {α : Type*}
instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (Mathlib.Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm
instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) := by
  refine @Quotient.fintype _ _ _ ?_
  intros x y
  apply List.decidablePerm
instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm