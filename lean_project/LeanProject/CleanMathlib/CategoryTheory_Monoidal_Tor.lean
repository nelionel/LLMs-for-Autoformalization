import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Preadditive
assert_not_exists ModuleCat.abelian
noncomputable section
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace CategoryTheory
variable (C : Type*) [Category C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]
@[simps]
def Tor (n : ℕ) : C ⥤ C ⥤ C where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map f := NatTrans.leftDerived ((tensoringLeft C).map f) n
@[simps! obj_obj]
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun f => NatTrans.leftDerived ((tensoringRight C).map f) n }
@[simp]
lemma Tor'_map_app' (n : ℕ) {X Y : C} (f : X ⟶ Y) (Z : C) :
    ((Tor' C n).map f).app Z = (Functor.leftDerived ((tensoringRight C).obj Z) n).map f := by
  rfl
@[simp]
lemma Tor'_obj_map (n : ℕ) {X Y : C} (Z : C) (f : X ⟶ Y) :
    ((Tor' C n).obj Z).map f = (NatTrans.leftDerived ((tensoringRight C).map f) n).app Z := rfl
lemma isZero_Tor_succ_of_projective (X Y : C) [Projective Y] (n : ℕ) :
    IsZero (((Tor C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ
lemma isZero_Tor'_succ_of_projective (X Y : C) [Projective X] (n : ℕ) :
    IsZero (((Tor' C (n + 1)).obj X).obj Y) := by
  apply Functor.isZero_leftDerived_obj_projective_succ
end CategoryTheory