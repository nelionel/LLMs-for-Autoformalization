import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.QPF.Multivariate.Basic
universe u
namespace MvQPF
open MvFunctor
variable (n : ℕ)
@[nolint unusedArguments]
def Const (A : Type*) (_v : TypeVec.{u} n) : Type _ := A
instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) := ⟨(default : A)⟩
namespace Const
open MvFunctor MvPFunctor
variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)
protected def mk (x : A) : Const n A α := x
protected def get (x : Const n A α) : A := x
@[simp]
protected theorem mk_get (x : Const n A α) : Const.mk (Const.get x) = x := rfl
@[simp]
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x := rfl
protected def map : Const n A α → Const n A β := fun x => x
instance MvFunctor : MvFunctor (Const n A) where map _f := Const.map
theorem map_mk (x : A) : f <$$> Const.mk x = Const.mk x := rfl
theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x := rfl
instance mvqpf : @MvQPF _ (Const n A) where
  P := MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := fun _ => const.get_mk _
  abs_map := fun _ => const.get_map _
end Const
end MvQPF