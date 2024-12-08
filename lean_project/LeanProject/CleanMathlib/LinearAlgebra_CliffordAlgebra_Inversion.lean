import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
variable {R M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
namespace CliffordAlgebra
variable (Q)
def invertibleιOfInvertible (m : M) [Invertible (Q m)] : Invertible (ι Q m) where
  invOf := ι Q (⅟ (Q m) • m)
  invOf_mul_self := by
    rw [map_smul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by
    rw [map_smul, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul, invOf_mul_self, map_one]
theorem invOf_ι (m : M) [Invertible (Q m)] [Invertible (ι Q m)] :
    ⅟ (ι Q m) = ι Q (⅟ (Q m) • m) := by
  letI := invertibleιOfInvertible Q m
  convert (rfl : ⅟ (ι Q m) = _)
theorem isUnit_ι_of_isUnit {m : M} (h : IsUnit (Q m)) : IsUnit (ι Q m) := by
  cases h.nonempty_invertible
  letI := invertibleιOfInvertible Q m
  exact isUnit_of_invertible (ι Q m)
theorem ι_mul_ι_mul_invOf_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ι Q a * ι Q b * ⅟ (ι Q a) = ι Q ((⅟ (Q a) * QuadraticMap.polar Q a b) • a - b) := by
  rw [invOf_ι, map_smul, mul_smul_comm, ι_mul_ι_mul_ι, ← map_smul, smul_sub, smul_smul, smul_smul,
    invOf_mul_self, one_smul]
theorem invOf_ι_mul_ι_mul_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ⅟ (ι Q a) * ι Q b * ι Q a = ι Q ((⅟ (Q a) * QuadraticMap.polar Q a b) • a - b) := by
  rw [invOf_ι, map_smul, smul_mul_assoc, smul_mul_assoc, ι_mul_ι_mul_ι, ← map_smul, smul_sub,
    smul_smul, smul_smul, invOf_mul_self, one_smul]
section
variable [Invertible (2 : R)]
def invertibleOfInvertibleι (m : M) [Invertible (ι Q m)] : Invertible (Q m) :=
  ExteriorAlgebra.invertibleAlgebraMapEquiv M (Q m) <|
    .algebraMapOfInvertibleAlgebraMap (equivExterior Q).toLinearMap (by simp) <|
      .copy (.mul ‹Invertible (ι Q m)› ‹Invertible (ι Q m)›) _ (ι_sq_scalar _ _).symm
theorem isUnit_of_isUnit_ι {m : M} (h : IsUnit (ι Q m)) : IsUnit (Q m) := by
  cases h.nonempty_invertible
  letI := invertibleOfInvertibleι Q m
  exact isUnit_of_invertible (Q m)
@[simp] theorem isUnit_ι_iff {m : M} : IsUnit (ι Q m) ↔ IsUnit (Q m) :=
  ⟨isUnit_of_isUnit_ι Q, isUnit_ι_of_isUnit Q⟩
end
end CliffordAlgebra