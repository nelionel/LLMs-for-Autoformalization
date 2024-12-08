import Mathlib.GroupTheory.OreLocalization.Cardinality
import Mathlib.RingTheory.OreLocalization.Ring
universe u
open Cardinal
namespace OreLocalization
variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]
theorem cardinalMk (hS : S ≤ nonZeroDivisorsRight R) : #(OreLocalization S R) = #R :=
  le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))
end OreLocalization