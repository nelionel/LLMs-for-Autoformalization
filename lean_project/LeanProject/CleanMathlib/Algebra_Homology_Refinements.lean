import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
open CategoryTheory
variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  (K : HomologicalComplex C c)
namespace HomologicalComplex
lemma eq_liftCycles_homologyπ_up_to_refinements {A : C} {i : ι} (γ : A ⟶ K.homology i)
    (j : ι) (hj : c.next i = j) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (z : A' ⟶ K.X i) (hz : z ≫ K.d i j = 0),
      π ≫ γ = K.liftCycles z j hj hz ≫ K.homologyπ i := by
  subst hj
  exact (K.sc i).eq_liftCycles_homologyπ_up_to_refinements γ
end HomologicalComplex