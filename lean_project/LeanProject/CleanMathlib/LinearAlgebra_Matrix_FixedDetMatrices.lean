import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]
def FixedDetMatrix (m : R) := { A : Matrix n n R // A.det = m }
namespace FixedDetMatrix
open ModularGroup Matrix SpecialLinearGroup MatrixGroups
lemma ext' {m : R} {A B : FixedDetMatrix n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  congr
@[ext]
lemma ext {m : R} {A B : FixedDetMatrix n R m} (h : ∀ i j , A.1 i j = B.1 i j) : A = B := by
  apply ext'
  ext i j
  apply h
instance (m : R) : SMul (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  smul g A := ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩
lemma smul_def (m : R) (g : SpecialLinearGroup n R) (A : (FixedDetMatrix n R m)) :
    g • A = ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ :=
  rfl
instance (m : R) : MulAction (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  one_smul b := by rw [smul_def]; simp only [coe_one, one_mul, Subtype.coe_eta]
  mul_smul x y b := by simp_rw [smul_def, ← mul_assoc, coe_mul]
lemma smul_coe (m : R) (g : SpecialLinearGroup n R) (A : FixedDetMatrix n R m) :
    (g • A).1 = g * A.1 := by
  rw [smul_def]
end FixedDetMatrix