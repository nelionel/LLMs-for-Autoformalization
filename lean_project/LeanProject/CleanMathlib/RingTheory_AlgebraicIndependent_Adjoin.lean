import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Defs
noncomputable section
open Function Set Subalgebra MvPolynomial Algebra
open scoped Classical
namespace AlgebraicIndependent
variable {ι : Type*}
variable {F E : Type*} {x : ι → E} [Field F] [Field E] [Algebra F E] (hx : AlgebraicIndependent F x)
include hx
def aevalEquivField :
    FractionRing (MvPolynomial ι F) ≃ₐ[F] ↥(IntermediateField.adjoin F (range x)) :=
  let i := IsFractionRing.liftAlgHom (K := FractionRing (MvPolynomial ι F))
    (algebraicIndependent_iff_injective_aeval.2 hx)
  (show _ ≃ₐ[F] i.fieldRange from AlgEquiv.ofInjectiveField i).trans <|
    IntermediateField.equivOfEq <|
      IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq (g := aeval x) (f := i)
        (by ext <;> simp [i]) (Algebra.adjoin_range_eq_range_aeval F x).symm
@[simp]
theorem aevalEquivField_apply_coe (a : FractionRing (MvPolynomial ι F)) :
    hx.aevalEquivField a =
      IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.2 hx) a := rfl
theorem aevalEquivField_algebraMap_apply_coe (a : MvPolynomial ι F) :
    hx.aevalEquivField (algebraMap _ _ a) = aeval x a := by
  simp
def reprField : IntermediateField.adjoin F (range x) →ₐ[F] FractionRing (MvPolynomial ι F) :=
  hx.aevalEquivField.symm
@[simp]
theorem lift_reprField (p) :
    IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.2 hx) (hx.reprField p) = p :=
  Subtype.ext_iff.1 (AlgEquiv.apply_symm_apply hx.aevalEquivField p)
theorem liftAlgHom_comp_reprField :
    (IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.2 hx)).comp hx.reprField =
      IntermediateField.val _ :=
  AlgHom.ext <| hx.lift_reprField
end AlgebraicIndependent