import Mathlib.Algebra.Module.Presentation.Basic
universe w v u
namespace Module
variable (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]
namespace Presentation
inductive tautological.R
  | add (m₁ m₂ : M)
  | smul (a : A) (m : M)
@[simps]
noncomputable def tautologicalRelations : Relations A where
  G := M
  R := tautological.R A M
  relation r := match r with
    | .add m₁ m₂ => Finsupp.single m₁ 1 + Finsupp.single m₂ 1 - Finsupp.single (m₁ + m₂) 1
    | .smul a m => a • Finsupp.single m 1 - Finsupp.single (a • m) 1
variable {A M} in
def tautologicalRelationsSolutionEquiv {N : Type w} [AddCommGroup N] [Module A N] :
    (tautologicalRelations A M).Solution N ≃ (M →ₗ[A] N) where
  toFun s :=
    { toFun := s.var
      map_add' := fun m₁ m₂ ↦ by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.add m₁ m₂)
      map_smul' := fun a m ↦ by
        symm
        rw [← sub_eq_zero]
        simpa using s.linearCombination_var_relation (.smul a m) }
  invFun f :=
    { var := f
      linearCombination_var_relation := by rintro (_ | _) <;> simp }
  left_inv _ := rfl
  right_inv _ := rfl
@[simps! var]
def tautologicalSolution : (tautologicalRelations A M).Solution M :=
  tautologicalRelationsSolutionEquiv.symm .id
def tautologicalSolutionIsPresentationCore :
    Relations.Solution.IsPresentationCore.{w} (tautologicalSolution A M) where
  desc s := tautologicalRelationsSolutionEquiv s
  postcomp_desc _ := rfl
  postcomp_injective h := by
    ext m
    exact Relations.Solution.congr_var h m
lemma tautologicalSolution_isPresentation :
    (tautologicalSolution A M).IsPresentation :=
  (tautologicalSolutionIsPresentationCore A M).isPresentation
@[simps!]
noncomputable def tautological : Presentation A M :=
  ofIsPresentation (tautologicalSolution_isPresentation A M)
end Presentation
end Module