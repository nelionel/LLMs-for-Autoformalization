import Mathlib.Data.QPF.Multivariate.Basic
universe u
open MvFunctor
namespace MvQPF
variable {n : ℕ}
variable {F : TypeVec.{u} n → Type u}
section repr
variable [q : MvQPF F]
variable {G : TypeVec.{u} n → Type u} [MvFunctor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
    MvQPF G where
  P := q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by dsimp; rw [abs_repr, FG_abs_repr]
  abs_map f p := by dsimp; rw [abs_map, FG_abs_map]
end repr
section Rel
variable (R : ∀ ⦃α⦄, F α → F α → Prop)
def Quot1 (α : TypeVec n) :=
  Quot (@R α)
instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩
section
variable [MvFunctor F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h
def Quot1.mvFunctor : MvFunctor (Quot1 R) where map := @Quot1.map _ _ R _ Hfunc
end
section
variable [q : MvQPF F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))
noncomputable def relQuot : @MvQPF _ (Quot1 R) :=
  @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl
end
end Rel
end MvQPF