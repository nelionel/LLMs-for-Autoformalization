import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
namespace WeierstrassCurve
variable (R : Type*) [CommRing R] (W : WeierstrassCurve R)
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩
lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0, c₄, b₂, b₄]
  norm_num1
lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0, Δ, b₂, b₄, b₆, b₈]
  norm_num1
def ofJ1728 : WeierstrassCurve R :=
  ⟨0, 0, 0, 1, 0⟩
lemma ofJ1728_c₄ : (ofJ1728 R).c₄ = -48 := by
  rw [ofJ1728, c₄, b₂, b₄]
  norm_num1
lemma ofJ1728_Δ : (ofJ1728 R).Δ = -64 := by
  rw [ofJ1728, Δ, b₂, b₄, b₆, b₈]
  norm_num1
variable {R} (j : R)
def ofJNe0Or1728 : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩
lemma ofJNe0Or1728_c₄ : (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1
lemma ofJNe0Or1728_Δ : (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1
variable (R) [W.IsElliptic]
instance [hu : Fact (IsUnit (3 : R))] : (ofJ0 R).IsElliptic := by
  rw [isElliptic_iff, ofJ0_Δ]
  convert (hu.out.pow 3).neg
  norm_num1
lemma ofJ0_j [Fact (IsUnit (3 : R))] : (ofJ0 R).j = 0 := by
  rw [j, ofJ0_c₄]
  ring1
instance [hu : Fact (IsUnit (2 : R))] : (ofJ1728 R).IsElliptic := by
  rw [isElliptic_iff, ofJ1728_Δ]
  convert (hu.out.pow 6).neg
  norm_num1
lemma ofJ1728_j [Fact (IsUnit (2 : R))] : (ofJ1728 R).j = 1728 := by
  rw [j, Units.inv_mul_eq_iff_eq_mul, ofJ1728_c₄, coe_Δ', ofJ1728_Δ]
  norm_num1
variable {R}
instance (j : R) [h1 : Fact (IsUnit j)] [h2 : Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).IsElliptic := by
  rw [isElliptic_iff, ofJNe0Or1728_Δ]
  exact (h1.out.pow 2).mul (h2.out.pow 9)
lemma ofJNe0Or1728_j (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).j = j := by
  rw [WeierstrassCurve.j, Units.inv_mul_eq_iff_eq_mul, ofJNe0Or1728_c₄, coe_Δ', ofJNe0Or1728_Δ]
  ring1
variable {F : Type*} [Field F] (j : F) [DecidableEq F]
def ofJ : WeierstrassCurve F :=
  if j = 0 then if (3 : F) = 0 then ofJ1728 F else ofJ0 F
  else if j = 1728 then ofJ1728 F else ofJNe0Or1728 j
lemma ofJ_0_of_three_ne_zero (h3 : (3 : F) ≠ 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg h3]
lemma ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 0 = ofJ1728 F := by
  rw [ofJ, if_pos rfl, if_pos h3]
lemma ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]
lemma ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 1728 = ofJ1728 F := by
  rw [ofJ, if_pos (by linear_combination 576 * h3), if_pos h3]
lemma ofJ_1728_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ofJ 1728 = ofJ1728 F := by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · rw [ofJ, show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num1,
      if_neg (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)), if_pos rfl]
lemma ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 1728 = ofJ0 F := by
  rw [ofJ, if_pos (by linear_combination 864 * h2),
    if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]
lemma ofJ_ne_0_ne_1728 (h0 : j ≠ 0) (h1728 : j ≠ 1728) : ofJ j = ofJNe0Or1728 j := by
  rw [ofJ, if_neg h0, if_neg h1728]
instance : (ofJ j).IsElliptic := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · have := Fact.mk (isUnit_of_mul_eq_one (2 : F) 2 (by linear_combination h3))
      rw [h0, ofJ_0_of_three_eq_zero h3]
      infer_instance
    · have := Fact.mk (Ne.isUnit h3)
      rw [h0, ofJ_0_of_three_ne_zero h3]
      infer_instance
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      rw [h1728, ofJ_1728_of_two_ne_zero h2]
      infer_instance
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      rw [ofJ_ne_0_ne_1728 j h0 h1728]
      infer_instance
lemma ofJ_j : (ofJ j).j = j := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · have := Fact.mk (isUnit_of_mul_eq_one (2 : F) 2 (by linear_combination h3))
      simp_rw [h0, ofJ_0_of_three_eq_zero h3, ofJ1728_j]
      linear_combination 576 * h3
    · have := Fact.mk (Ne.isUnit h3)
      simp_rw [h0, ofJ_0_of_three_ne_zero h3, ofJ0_j]
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      simp_rw [h1728, ofJ_1728_of_two_ne_zero h2, ofJ1728_j]
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      simp_rw [ofJ_ne_0_ne_1728 j h0 h1728, ofJNe0Or1728_j]
instance : Inhabited { W : WeierstrassCurve F // W.IsElliptic } := ⟨⟨ofJ 37, inferInstance⟩⟩
end WeierstrassCurve