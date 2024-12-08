import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Ordinary
universe v u
open CategoryTheory Category Simplicial MonoidalCategory
namespace CategoryTheory
variable (C : Type u) [Category.{v} C]
abbrev SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C
namespace SimplicialCategory
variable [SimplicialCategory C]
variable {C}
abbrev sHom (K L : C) : SSet.{v} := K ⟶[SSet] L
abbrev sHomComp (K L M : C) : sHom K L ⊗ sHom L M ⟶ sHom K M := eComp SSet K L M
def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _[0] :=
  (eHomEquiv SSet).trans (sHom K L).unitHomEquiv
variable (C) in
noncomputable abbrev sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} := eHomFunctor _ _
end SimplicialCategory
end CategoryTheory