import Mathlib.AlgebraicTopology.DoldKan.EquivalencePseudoabelian
import Mathlib.AlgebraicTopology.DoldKan.Normalized
noncomputable section
open CategoryTheory Category Idempotents
variable {A : Type*} [Category A] [Abelian A]
namespace CategoryTheory
namespace Abelian
namespace DoldKan
open AlgebraicTopology.DoldKan
def N : SimplicialObject A ⥤ ChainComplex A ℕ :=
  AlgebraicTopology.normalizedMooreComplex A
def Γ : ChainComplex A ℕ ⥤ SimplicialObject A :=
  Idempotents.DoldKan.Γ
@[simps!]
def comparisonN : (N : SimplicialObject A ⥤ _) ≅ Idempotents.DoldKan.N :=
  calc
    N ≅ N ⋙ 𝟭 _ := Functor.leftUnitor N
    _ ≅ N ⋙ (toKaroubiEquivalence _).functor ⋙ (toKaroubiEquivalence _).inverse :=
          isoWhiskerLeft _ (toKaroubiEquivalence _).unitIso
    _ ≅ (N ⋙ (toKaroubiEquivalence _).functor) ⋙ (toKaroubiEquivalence _).inverse :=
          Iso.refl _
    _ ≅ N₁ ⋙ (toKaroubiEquivalence _).inverse :=
          isoWhiskerRight (N₁_iso_normalizedMooreComplex_comp_toKaroubi A).symm _
    _ ≅ Idempotents.DoldKan.N := Iso.refl _
@[simps! functor]
def equivalence : SimplicialObject A ≌ ChainComplex A ℕ :=
  (Idempotents.DoldKan.equivalence (C := A)).changeFunctor comparisonN.symm
theorem equivalence_inverse : (equivalence : SimplicialObject A ≌ _).inverse = Γ :=
  rfl
end DoldKan
end Abelian
end CategoryTheory