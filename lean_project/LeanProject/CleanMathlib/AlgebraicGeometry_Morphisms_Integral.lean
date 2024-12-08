import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.RingHom.Integral
universe v u
open CategoryTheory TopologicalSpace Opposite MorphismProperty
namespace AlgebraicGeometry
@[mk_iff]
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) extends IsAffineHom f : Prop where
  integral_app (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).IsIntegral
namespace IsIntegralHom
instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤) := by
  show HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]
instance : IsStableUnderComposition @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition
instance : IsStableUnderBaseChange @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange
instance : ContainsIdentities @IsIntegralHom :=
  ⟨fun X ↦ ⟨fun _ _ ↦ by simpa using RingHom.isIntegral_of_surjective _ (Equiv.refl _).surjective⟩⟩
instance : IsMultiplicative @IsIntegralHom where
end IsIntegralHom
end AlgebraicGeometry