import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Logic.UnivLE
universe w w₀ w₁ v u
namespace Module
variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]
namespace Relations
variable [IsEmpty relations.R]
@[simps]
noncomputable def solutionFinsupp : relations.Solution (relations.G →₀ A) where
  var g := Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r
noncomputable def solutionFinsupp.isPresentationCore :
    Solution.IsPresentationCore.{w} relations.solutionFinsupp where
  desc s := Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h
lemma solutionFinsupp_isPresentation :
    relations.solutionFinsupp.IsPresentation :=
  (solutionFinsupp.isPresentationCore relations).isPresentation
variable {relations}
lemma Solution.IsPresentation.free {solution : relations.Solution M}
    (h : solution.IsPresentation) :
    Module.Free A M :=
  Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)
end Relations
variable (A)
@[simps! G R var]
noncomputable def presentationFinsupp (G : Type w₀) :
    Presentation.{w₀, w₁} A (G →₀ A) where
  G := G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := Relations.solutionFinsupp_isPresentation _
lemma free_iff_exists_presentation :
    Free A M ↔ ∃ (p : Presentation.{v, w₁} A M), IsEmpty p.R := by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm,
      by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free
end Module