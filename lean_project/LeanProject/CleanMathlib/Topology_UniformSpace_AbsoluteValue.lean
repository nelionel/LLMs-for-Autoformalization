import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.UniformSpace.OfFun
open Set Function Filter Uniformity
namespace AbsoluteValue
variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {R : Type*} [CommRing R] (abv : AbsoluteValue R 𝕜)
def uniformSpace : UniformSpace R :=
  .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun _ _ _ => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩
theorem hasBasis_uniformity :
    𝓤[abv.uniformSpace].HasBasis ((0 : 𝕜) < ·) fun ε => { p : R × R | abv (p.2 - p.1) < ε } :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _
end AbsoluteValue