import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Types
import Mathlib.Control.Basic 
namespace CategoryTheory
section
universe u
variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]
@[simps!]
def ofTypeMonad : Monad (Type u) where
  toFunctor := ofTypeFunctor m
  η := ⟨@pure m _, fun _ _ f => funext fun x => (LawfulApplicative.map_pure f x).symm⟩
  μ := ⟨@joinM m _, fun α β (f : α → β) => funext fun a => by apply joinM_map_map⟩
  assoc α := funext fun a => by apply joinM_map_joinM
  left_unit α := funext fun a => by apply joinM_pure
  right_unit α := funext fun a => by apply joinM_map_pure
@[simps]
def eq : KleisliCat m ≌ Kleisli (ofTypeMonad m) where
  functor :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun f g => by
        funext t
        change _ = joinM (g <$> (f t))
        simp only [joinM, seq_bind_eq, Function.id_comp]
        rfl }
  inverse :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun f g => by
        letI : _root_.Monad (ofTypeMonad m).obj :=
          show _root_.Monad m from inferInstance
        letI : LawfulMonad (ofTypeMonad m).obj :=
          show LawfulMonad m from inferInstance
        funext t
        dsimp
        change joinM (g <$> (f t)) = _
        simp only [joinM, seq_bind_eq, Function.id_comp]
        rfl }
  unitIso := by
    refine NatIso.ofComponents (fun X => Iso.refl X) fun f => ?_
    change f >=> pure = pure >=> f
    simp [functor_norm]
  counitIso := NatIso.ofComponents fun X => Iso.refl X
end
end CategoryTheory