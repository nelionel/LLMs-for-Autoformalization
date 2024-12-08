import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.GroupTheory.OreLocalization.Cardinality
universe u
open Cardinal
namespace Localization
variable {M : Type u} [CommMonoid M] (S : Submonoid M)
@[to_additive]
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S
end Localization