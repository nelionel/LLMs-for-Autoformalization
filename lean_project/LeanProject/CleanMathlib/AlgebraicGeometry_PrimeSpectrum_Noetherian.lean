import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Topology.NoetherianSpace
universe u v
namespace PrimeSpectrum
open TopologicalSpace
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
instance : NoetherianSpace (PrimeSpectrum R) :=
  ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT
lemma _root_.minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite :=
  minimalPrimes.equivIrreducibleComponents R
    |>.set_finite_iff
    |>.mpr NoetherianSpace.finite_irreducibleComponents
lemma finite_setOf_isMin :
    {x : PrimeSpectrum R | IsMin x }.Finite := by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)
end PrimeSpectrum