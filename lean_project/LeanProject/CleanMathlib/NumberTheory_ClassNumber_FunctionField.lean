import Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.FunctionField
namespace FunctionField
open scoped Polynomial
variable (Fq F : Type*) [Field Fq] [Fintype Fq] [Field F]
variable [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
variable [IsScalarTower Fq[X] (RatFunc Fq) F]
variable [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
open scoped Classical
namespace RingOfIntegers
open FunctionField
noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))
end RingOfIntegers
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff
end FunctionField