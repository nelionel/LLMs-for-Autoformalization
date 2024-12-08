import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Rat.Cast.Defs
namespace algebraMap
universe u v w u₁ v₁
section FieldNontrivial
variable {R A : Type*} [Field R] [CommSemiring A] [Nontrivial A] [Algebra R A]
@[norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (algebraMap R A).injective.eq_iff
@[norm_cast]
theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 := map_eq_zero _
end FieldNontrivial
section SemifieldSemidivisionRing
variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]
@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r
@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s
@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z :=
  map_zpow₀ (algebraMap R A) r z
end SemifieldSemidivisionRing
section FieldDivisionRing
variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]
@[norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q
end FieldDivisionRing
end algebraMap