import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
namespace IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R]
def ResidueField :=
  R ⧸ maximalIdeal R
instance ResidueFieldCommRing : CommRing (ResidueField R) :=
  show CommRing (R ⧸ maximalIdeal R) from inferInstance
instance ResidueFieldInhabited : Inhabited (ResidueField R) :=
  show Inhabited (R ⧸ maximalIdeal R) from inferInstance
noncomputable instance ResidueField.field : Field (ResidueField R) :=
  Ideal.Quotient.field (maximalIdeal R)
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _
end IsLocalRing
@[deprecated (since := "2024-11-11")] alias LocalRing.ResidueField := IsLocalRing.ResidueField
@[deprecated (since := "2024-11-11")] alias LocalRing.residue := IsLocalRing.residue