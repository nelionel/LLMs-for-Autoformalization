import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Shift.Basic
open CategoryTheory Category
namespace CategoryTheory
variable {C : Type*} [Category C] (P : C → Prop)
  {A : Type*} [AddMonoid A] [HasShift C A]
def PredicateShift (a : A) : C → Prop := fun X => P (X⟦a⟧)
lemma predicateShift_iff (a : A) (X : C) : PredicateShift P a X ↔ P (X⟦a⟧) := Iff.rfl
instance predicateShift_closedUnderIsomorphisms (a : A) [ClosedUnderIsomorphisms P] :
    ClosedUnderIsomorphisms (PredicateShift P a) where
  of_iso e hX := mem_of_iso P ((shiftFunctor C a).mapIso e) hX
variable (A)
@[simp]
lemma predicateShift_zero [ClosedUnderIsomorphisms P] : PredicateShift P (0 : A) = P := by
  ext X
  exact mem_iff_of_iso P ((shiftFunctorZero C A).app X)
variable {A}
lemma predicateShift_predicateShift (a b c : A) (h : a + b = c) [ClosedUnderIsomorphisms P] :
    PredicateShift (PredicateShift P b) a = PredicateShift P c := by
  ext X
  exact mem_iff_of_iso _ ((shiftFunctorAdd' C a b c h).symm.app X)
end CategoryTheory