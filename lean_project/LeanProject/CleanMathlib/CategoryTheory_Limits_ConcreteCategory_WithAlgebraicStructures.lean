import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.CategoryTheory.Elementwise
universe t w v u r
open CategoryTheory
namespace CategoryTheory.Limits.Concrete
attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort
variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max t w} C] {J : Type w} [Category.{r} J]
section zero
theorem colimit_rep_eq_zero
    (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]
    [∀ c : C, Zero c] [∀ {c c' : C}, ZeroHomClass (c ⟶ c') c c'] [HasColimit F]
    (j : J) (x : F.obj j) (hx : colimit.ι F j x = 0) :
    ∃ (j' : J) (i : j ⟶ j'), F.map i x = 0 := by
  rw [show 0 = colimit.ι F j 0 by simp, colimit_rep_eq_iff_exists] at hx
  obtain ⟨j', i, y, g⟩ := hx
  exact ⟨j', i, g ▸ by simp⟩
end zero
section module
lemma colimit_no_zero_smul_divisor
    (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J] [HasColimit F]
    (R : Type*) [Semiring R]
    [∀ c : C, AddCommMonoid c] [∀ c : C, Module R c]
    [∀ {c c' : C}, LinearMapClass (c ⟶ c') R c c']
    (r : R) (H : ∃ (j' : J), ∀ (j : J) (_ : j' ⟶ j), ∀ (c : F.obj j), r • c = 0 → c = 0)
    (x : (forget C).obj (colimit F)) (hx : r • x = 0) : x = 0 := by
  classical
  obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep F x
  rw [← map_smul] at hx
  obtain ⟨j', i, h⟩ := Concrete.colimit_rep_eq_zero (hx := hx)
  obtain ⟨j'', H⟩ := H
  simpa [elementwise_of% (colimit.w F), map_zero] using congr(colimit.ι F _
    $(H (IsFiltered.sup {j, j', j''} { ⟨j, j', by simp, by simp, i⟩ })
      (IsFiltered.toSup _ _ <| by simp)
      (F.map (IsFiltered.toSup _ _ <| by simp) x)
      (by rw [← IsFiltered.toSup_commutes (f := i) (mY := by simp) (mf := by simp), F.map_comp,
        comp_apply, ← map_smul, ← map_smul, h, map_zero])))
end module
end CategoryTheory.Limits.Concrete