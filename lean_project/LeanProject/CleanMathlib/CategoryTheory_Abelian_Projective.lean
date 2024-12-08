import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
universe v u
namespace CategoryTheory
open Limits Projective Opposite
variable {C : Type u} [Category.{v} C] [Abelian C]
noncomputable instance preservesHomology_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    (preadditiveCoyonedaObj (op P)).PreservesHomology := by
  haveI := (projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' P).mp hP
  haveI := @Functor.preservesEpimorphisms_of_preserves_of_reflects _ _ _ _ _ _ _ _ this _
  apply Functor.preservesHomology_of_preservesEpis_and_kernels
noncomputable instance preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj (op P)) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj (op P))] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj']
  dsimp
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj (op P))
  infer_instance
end CategoryTheory