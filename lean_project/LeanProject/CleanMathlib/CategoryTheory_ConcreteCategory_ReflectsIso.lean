import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso
universe u
namespace CategoryTheory
instance : (forget (Type u)).ReflectsIsomorphisms where reflects _ _ _ {i} := i
variable (C : Type (u + 1)) [Category C] [ConcreteCategory.{u} C]
variable (D : Type (u + 1)) [Category D] [ConcreteCategory.{u} D]
theorem reflectsIsomorphisms_forget₂ [HasForget₂ C D] [(forget C).ReflectsIsomorphisms] :
    (forget₂ C D).ReflectsIsomorphisms :=
  { reflects := fun X Y f {i} => by
      haveI i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      haveI : IsIso ((forget C).map f) := by
        have := @HasForget₂.forget_comp C D
        rwa [← this]
      apply isIso_of_reflects_iso f (forget C) }
end CategoryTheory