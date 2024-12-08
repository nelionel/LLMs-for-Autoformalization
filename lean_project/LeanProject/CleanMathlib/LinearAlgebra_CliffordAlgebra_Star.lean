import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}
namespace CliffordAlgebra
instance instStarRing : StarRing (CliffordAlgebra Q) where
  star x := reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]
theorem star_def (x : CliffordAlgebra Q) : star x = reverse (involute x) :=
  rfl
theorem star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x) :=
  reverse_involute _
@[simp]
theorem star_ι (m : M) : star (ι Q m) = -ι Q m := by rw [star_def, involute_ι, map_neg, reverse_ι]
@[simp]
theorem star_smul (r : R) (x : CliffordAlgebra Q) : star (r • x) = r • star x := by
  rw [star_def, star_def, map_smul, map_smul]
@[simp]
theorem star_algebraMap (r : R) :
    star (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (CliffordAlgebra Q) r := by
  rw [star_def, involute.commutes, reverse.commutes]
end CliffordAlgebra