import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])
universe s u v w
@[ext]
structure WeierstrassCurve (R : Type u) where
  a₁ : R
  a₂ : R
  a₃ : R
  a₄ : R
  a₆ : R
namespace WeierstrassCurve
instance instInhabited {R : Type u} [Inhabited R] :
    Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
section Quantity
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1
section CharTwo
variable [CharP R 2]
lemma b₂_of_char_two : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2
lemma b₄_of_char_two : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2
lemma b₆_of_char_two : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2
lemma b₈_of_char_two :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 + W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2
lemma c₄_of_char_two : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄, b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2
lemma c₆_of_char_two : W.c₆ = W.a₁ ^ 6 := by
  rw [c₆, b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2
lemma Δ_of_char_two : W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3 := by
  rw [Δ, b₂_of_char_two, b₄_of_char_two, b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2
lemma b_relation_of_char_two : W.b₂ * W.b₆ = W.b₄ ^ 2 := by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2
lemma c_relation_of_char_two : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2
end CharTwo
section CharThree
variable [CharP R 3]
lemma b₂_of_char_three : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3
lemma b₄_of_char_three : W.b₄ = -W.a₄ + W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3
lemma b₆_of_char_three : W.b₆ = W.a₃ ^ 2 + W.a₆ := by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3
lemma b₈_of_char_three :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3
lemma c₄_of_char_three : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3
lemma c₆_of_char_three : W.c₆ = -W.b₂ ^ 3 := by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3
lemma Δ_of_char_three : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3
lemma b_relation_of_char_three : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3
lemma c_relation_of_char_three : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3
end CharThree
end Quantity
section BaseChange
variable {A : Type v} [CommRing A] (φ : R →+* A)
@[simps]
def map : WeierstrassCurve A :=
  ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄, φ W.a₆⟩
variable (A)
abbrev baseChange [Algebra R A] : WeierstrassCurve A :=
  W.map <| algebraMap R A
variable {A}
@[simp]
lemma map_b₂ : (W.map φ).b₂ = φ W.b₂ := by
  simp only [b₂, map_a₁, map_a₂]
  map_simp
@[simp]
lemma map_b₄ : (W.map φ).b₄ = φ W.b₄ := by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp
@[simp]
lemma map_b₆ : (W.map φ).b₆ = φ W.b₆ := by
  simp only [b₆, map_a₃, map_a₆]
  map_simp
@[simp]
lemma map_b₈ : (W.map φ).b₈ = φ W.b₈ := by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp
@[simp]
lemma map_c₄ : (W.map φ).c₄ = φ W.c₄ := by
  simp only [c₄, map_b₂, map_b₄]
  map_simp
@[simp]
lemma map_c₆ : (W.map φ).c₆ = φ W.c₆ := by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp
@[simp]
lemma map_Δ : (W.map φ).Δ = φ W.Δ := by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp
@[simp]
lemma map_id : W.map (RingHom.id R) = W :=
  rfl
lemma map_map {B : Type w} [CommRing B] (ψ : A →+* B) : (W.map φ).map ψ = W.map (ψ.comp φ) :=
  rfl
@[simp]
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A →ₐ[S] B) : (W.baseChange A).map ψ = W.baseChange B :=
  congr_arg W.map <| ψ.comp_algebraMap_of_tower R
lemma map_injective {φ : R →+* A} (hφ : Function.Injective φ) :
    Function.Injective <| map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hφ <;> assumption
end BaseChange
section TorsionPolynomial
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩
lemma twoTorsionPolynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.disc]
  ring1
section CharTwo
variable [CharP R 2]
lemma twoTorsionPolynomial_of_char_two : W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2
lemma twoTorsionPolynomial_disc_of_char_two : W.twoTorsionPolynomial.disc = 0 := by
  linear_combination W.twoTorsionPolynomial_disc + 8 * W.Δ * CharP.cast_eq_zero R 2
end CharTwo
section CharThree
variable [CharP R 3]
lemma twoTorsionPolynomial_of_char_three : W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3
lemma twoTorsionPolynomial_disc_of_char_three : W.twoTorsionPolynomial.disc = W.Δ := by
  linear_combination W.twoTorsionPolynomial_disc + 5 * W.Δ * CharP.cast_eq_zero R 3
end CharThree
lemma twoTorsionPolynomial_disc_isUnit (hu : IsUnit (2 : R)) :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ := by
  rw [twoTorsionPolynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right <| hu.pow 4
lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] (hu : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  ((W.twoTorsionPolynomial_disc_isUnit hu).mpr hΔ).ne_zero
end TorsionPolynomial
@[mk_iff]
protected class IsElliptic : Prop where
  isUnit : IsUnit W.Δ
variable [W.IsElliptic]
lemma isUnit_Δ : IsUnit W.Δ := IsElliptic.isUnit
noncomputable def Δ' : Rˣ := W.isUnit_Δ.unit
@[simp]
lemma coe_Δ' : W.Δ' = W.Δ := rfl
noncomputable def j : R :=
  W.Δ'⁻¹ * W.c₄ ^ 3
lemma j_eq_zero_iff' : W.j = 0 ↔ W.c₄ ^ 3 = 0 := by
  rw [j, Units.mul_right_eq_zero]
lemma j_eq_zero (h : W.c₄ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff', h, zero_pow three_ne_zero]
lemma j_eq_zero_iff [IsReduced R] : W.j = 0 ↔ W.c₄ = 0 := by
  rw [j_eq_zero_iff', IsReduced.pow_eq_zero_iff three_ne_zero]
section CharTwo
variable [CharP R 2]
lemma j_of_char_two : W.j = W.Δ'⁻¹ * W.a₁ ^ 12 := by
  rw [j, W.c₄_of_char_two, ← pow_mul]
lemma j_eq_zero_iff_of_char_two' : W.j = 0 ↔ W.a₁ ^ 12 = 0 := by
  rw [j_of_char_two, Units.mul_right_eq_zero]
lemma j_eq_zero_of_char_two (h : W.a₁ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_two', h, zero_pow (Nat.succ_ne_zero _)]
lemma j_eq_zero_iff_of_char_two [IsReduced R] : W.j = 0 ↔ W.a₁ = 0 := by
  rw [j_eq_zero_iff_of_char_two', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]
end CharTwo
section CharThree
variable [CharP R 3]
lemma j_of_char_three : W.j = W.Δ'⁻¹ * W.b₂ ^ 6 := by
  rw [j, W.c₄_of_char_three, ← pow_mul]
lemma j_eq_zero_iff_of_char_three' : W.j = 0 ↔ W.b₂ ^ 6 = 0 := by
  rw [j_of_char_three, Units.mul_right_eq_zero]
lemma j_eq_zero_of_char_three (h : W.b₂ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_three', h, zero_pow (Nat.succ_ne_zero _)]
lemma j_eq_zero_iff_of_char_three [IsReduced R] : W.j = 0 ↔ W.b₂ = 0 := by
  rw [j_eq_zero_iff_of_char_three', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]
end CharThree
lemma twoTorsionPolynomial_disc_ne_zero_of_isElliptic [Nontrivial R] (hu : IsUnit (2 : R)) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  W.twoTorsionPolynomial_disc_ne_zero hu W.isUnit_Δ
section BaseChange
variable {A : Type v} [CommRing A] (φ : R →+* A)
instance : (W.map φ).IsElliptic := by
  simp only [isElliptic_iff, map_Δ, W.isUnit_Δ.map]
set_option linter.docPrime false in
lemma coe_map_Δ' : (W.map φ).Δ' = φ W.Δ' := by
  rw [coe_Δ', map_Δ, coe_Δ']
set_option linter.docPrime false in
@[simp]
lemma map_Δ' : (W.map φ).Δ' = Units.map φ W.Δ' := by
  ext
  exact W.coe_map_Δ' φ
set_option linter.docPrime false in
lemma coe_inv_map_Δ' : (W.map φ).Δ'⁻¹ = φ ↑W.Δ'⁻¹ := by
  simp
set_option linter.docPrime false in
lemma inv_map_Δ' : (W.map φ).Δ'⁻¹ = Units.map φ W.Δ'⁻¹ := by
  simp
@[simp]
lemma map_j : (W.map φ).j = φ W.j := by
  rw [j, coe_inv_map_Δ', map_c₄, j, map_mul, map_pow]
end BaseChange
end WeierstrassCurve