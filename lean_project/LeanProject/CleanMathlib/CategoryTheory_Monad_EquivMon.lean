import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Mon_
namespace CategoryTheory
open Category
universe v u 
variable {C : Type u} [Category.{v} C]
namespace Monad
attribute [local instance] endofunctorMonoidalCategory
@[simps]
def toMon (M : Monad C) : Mon_ (C ⥤ C) where
  X := (M : C ⥤ C)
  one := M.η
  mul := M.μ
  mul_assoc := by ext; simp [M.assoc]
variable (C)
@[simps]
def monadToMon : Monad C ⥤ Mon_ (C ⥤ C) where
  obj := toMon
  map f := { hom := f.toNatTrans }
variable {C}
@[simps η μ]
def ofMon (M : Mon_ (C ⥤ C)) : Monad C where
  toFunctor := M.X
  η := M.one
  μ := M.mul
  left_unit := fun X => by
    erw [← whiskerLeft_app, ← NatTrans.comp_app, M.mul_one]
    rfl
  right_unit := fun X => by
    erw [← whiskerRight_app, ← NatTrans.comp_app, M.one_mul]
    rfl
  assoc := fun X => by
    rw [← whiskerLeft_app, ← whiskerRight_app, ← NatTrans.comp_app]
    erw [M.mul_assoc]
    simp
@[simp] lemma ofMon_obj (M : Mon_ (C ⥤ C)) (X : C) : (ofMon M).obj X = M.X.obj X := rfl
variable (C)
@[simps]
def monToMonad : Mon_ (C ⥤ C) ⥤ Monad C where
  obj := ofMon
  map {X Y} f :=
    { f.hom with
      app_η := by
        intro X
        erw [← NatTrans.comp_app, f.one_hom]
        simp only [Functor.id_obj, ofMon_obj, ofMon_η]
      app_μ := by
        intro Z
        erw [← NatTrans.comp_app, f.mul_hom]
        dsimp
        simp only [Category.assoc, NatTrans.naturality, ofMon_obj, ofMon] }
@[simps]
def monadMonEquiv : Monad C ≌ Mon_ (C ⥤ C) where
  functor := monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }
example (A : Monad C) {X : C} : ((monadMonEquiv C).unitIso.app A).hom.app X = 𝟙 _ :=
  rfl
end Monad
end CategoryTheory