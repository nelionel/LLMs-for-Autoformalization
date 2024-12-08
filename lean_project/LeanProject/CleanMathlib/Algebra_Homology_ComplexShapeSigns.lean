import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.CategoryTheory.GradedObject.Trifunctor
variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)
class TotalComplexShape where
  π : I₁ × I₂ → I₁₂
  ε₁ : I₁ × I₂ → ℤˣ
  ε₂ : I₁ × I₂ → ℤˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩
namespace ComplexShape
variable [TotalComplexShape c₁ c₂ c₁₂]
abbrev π (i : I₁ × I₂) : I₁₂ := TotalComplexShape.π c₁ c₂ c₁₂ i
abbrev ε₁ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₁ c₁ c₂ c₁₂ i
abbrev ε₂ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₂ c₁ c₂ c₁₂ i
variable {c₁}
lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂
lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)
lemma prev_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)
variable (c₁) {c₂}
lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h
lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)
lemma prev_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)
variable {c₁}
lemma ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ =
      - ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  TotalComplexShape.ε₂_ε₁ h₁ h₂
lemma ε₁_ε₂ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ =
      - ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂')), mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc, ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul, neg_mul, neg_mul, mul_neg, neg_inj, ← mul_assoc, ← mul_assoc,
      Int.units_mul_self, one_mul])
section
variable {I : Type*} [AddMonoid I] (c : ComplexShape I)
class TensorSigns where
  ε' : Multiplicative I →* ℤˣ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε'_succ (p q : I) (hpq : c.Rel p q) : ε' q = - ε' p
variable [TensorSigns c]
abbrev ε (i : I) : ℤˣ := TensorSigns.ε' c i
lemma rel_add {p q : I} (hpq : c.Rel p q) (r : I) : c.Rel (p + r) (q + r) :=
  TensorSigns.rel_add _ _ _ hpq
lemma add_rel (r : I) {p q : I} (hpq : c.Rel p q) : c.Rel (r + p) (r + q) :=
  TensorSigns.add_rel _ _ _ hpq
@[simp]
lemma ε_zero : c.ε 0 = 1 := by
  apply MonoidHom.map_one
lemma ε_succ {p q : I} (hpq : c.Rel p q) : c.ε q = - c.ε p :=
  TensorSigns.ε'_succ p q hpq
lemma ε_add (p q : I) : c.ε (p + q) = c.ε p * c.ε q := by
  apply MonoidHom.map_mul
lemma next_add (p q : I) (hp : c.Rel p (c.next p)) :
    c.next (p + q) = c.next p + q :=
  c.next_eq' (c.rel_add hp q)
lemma next_add' (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q :=
  c.next_eq' (c.add_rel p hq)
@[simps]
instance : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul, one_mul, mul_one, c.ε_succ h, neg_neg]
instance : TensorSigns (ComplexShape.down ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; omega
  add_rel p q r (hpq : q + 1 = p) := by dsimp; omega
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one, neg_neg]
@[simp]
lemma ε_down_ℕ (n : ℕ) : (ComplexShape.down ℕ).ε n = (-1 : ℤˣ) ^ n := rfl
instance : TensorSigns (ComplexShape.up ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]
@[simp]
lemma ε_up_ℤ (n : ℤ) : (ComplexShape.up ℤ).ε n = n.negOnePow := rfl
end
section
variable (c₁ c₂)
variable [TotalComplexShape c₁₂ c₃ c] [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c]
class Associative : Prop where
  assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩
  ε₁_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂)
  ε₂_ε₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂)
  ε₂_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) =
      (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃))
variable [Associative c₁ c₂ c₃ c₁₂ c₂₃ c]
lemma assoc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩ = π c₁ c₂₃ c ⟨i₁, π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ := by
  apply Associative.assoc
lemma associative_ε₁_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₁ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₁ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associative.ε₁_eq_mul
lemma associative_ε₂_ε₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₁ c₂ c₃ c₂₃ (i₂, i₃) =
      ε₁ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) * ε₂ c₁ c₂ c₁₂ (i₁, i₂) := by
  apply Associative.ε₂_ε₁
lemma associative_ε₂_eq_mul (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    ε₂ c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) =
      (ε₂ c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) * ε₂ c₂ c₃ c₂₃ (i₂, i₃)) := by
  apply Associative.ε₂_eq_mul
def r : I₁ × I₂ × I₃ → J := fun ⟨i₁, i₂, i₃⟩ ↦ π c₁₂ c₃ c ⟨π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃⟩
open CategoryTheory
@[reducible]
def ρ₁₂ : GradedObject.BifunctorComp₁₂IndexData (r c₁ c₂ c₃ c₁₂ c) where
  I₁₂ := I₁₂
  p := π c₁ c₂ c₁₂
  q := π c₁₂ c₃ c
  hpq _ := rfl
@[reducible]
def ρ₂₃ : GradedObject.BifunctorComp₂₃IndexData (r c₁ c₂ c₃ c₁₂ c) where
  I₂₃ := I₂₃
  p := π c₂ c₃ c₂₃
  q := π c₁ c₂₃ c
  hpq := fun ⟨i₁, i₂, i₃⟩ ↦ (assoc c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃).symm
end
instance {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] :
    Associative c c c c c c where
  assoc := add_assoc
  ε₁_eq_mul _ _ _ := by dsimp; rw [one_mul]
  ε₂_ε₁ _ _ _ := by dsimp; rw [one_mul, mul_one]
  ε₂_eq_mul _ _ _ := by dsimp; rw [ε_add]
end ComplexShape
class TotalComplexShapeSymmetry [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂] where
  symm (i₁ : I₁) (i₂ : I₂) : ComplexShape.π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  σ (i₁ : I₁) (i₂ : I₂) : ℤˣ
  σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ i₁ i₂ * ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁' i₂
  σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ i₁ i₂ * ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁ i₂'
namespace ComplexShape
variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂]
abbrev σ (i₁ : I₁) (i₂ : I₂) : ℤˣ := TotalComplexShapeSymmetry.σ c₁ c₂ c₁₂ i₁ i₂
lemma π_symm (i₁ : I₁) (i₂ : I₂) :
    π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm
@[simps]
def symmetryEquiv (j : I₁₂) :
    (π c₂ c₁ c₁₂ ⁻¹' {j}) ≃ (π c₁ c₂ c₁₂ ⁻¹' {j}) where
  toFun := fun ⟨⟨i₂, i₁⟩, h⟩ => ⟨⟨i₁, i₂⟩, by simpa [π_symm] using h⟩
  invFun := fun ⟨⟨i₁, i₂⟩, h⟩ => ⟨⟨i₂, i₁⟩, by simpa [π_symm] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable {c₁}
lemma σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁' i₂ :=
  TotalComplexShapeSymmetry.σ_ε₁ h₁ i₂
variable (c₁) {c₂}
lemma σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁ i₂' :=
  TotalComplexShapeSymmetry.σ_ε₂ i₁ h₂
@[simps]
instance : TotalComplexShapeSymmetry (up ℤ) (up ℤ) (up ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, ← Int.negOnePow_add, add_comm q, add_mul, one_mul, Int.negOnePow_add,
      Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, ← Int.negOnePow_add, mul_add, mul_one]
end ComplexShape
def TotalComplexShapeSymmetry.symmetry [TotalComplexShape c₁ c₂ c₁₂]
    [TotalComplexShape c₂ c₁ c₁₂] [TotalComplexShapeSymmetry c₁ c₂ c₁₂] :
    TotalComplexShapeSymmetry c₂ c₁ c₁₂ where
  symm i₂ i₁ := (ComplexShape.π_symm c₁ c₂ c₁₂ i₁ i₂).symm
  σ i₂ i₁ := ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂
  σ_ε₁ {i₂ i₂'} h₂ i₁ := by
    dsimp
    apply mul_right_cancel (b := ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, ComplexShape.σ_ε₂ c₁ c₁₂ i₁ h₂, mul_comm, ← mul_assoc,
      Int.units_mul_self, one_mul, mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]
  σ_ε₂ i₂ i₁ i₁' h₁ := by
    dsimp
    apply mul_right_cancel (b := ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂))
    rw [mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, ComplexShape.σ_ε₁ c₂ c₁₂ h₁ i₂, mul_comm, ← mul_assoc,
      Int.units_mul_self, one_mul, mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]
class TotalComplexShapeSymmetrySymmetry [TotalComplexShape c₁ c₂ c₁₂]
    [TotalComplexShape c₂ c₁ c₁₂] [TotalComplexShapeSymmetry c₁ c₂ c₁₂]
    [TotalComplexShapeSymmetry c₂ c₁ c₁₂] : Prop where
  σ_symm i₁ i₂ : ComplexShape.σ c₂ c₁ c₁₂ i₂ i₁ = ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂
namespace ComplexShape
variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂] [TotalComplexShapeSymmetry c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetrySymmetry c₁ c₂ c₁₂]
lemma σ_symm (i₁ : I₁) (i₂ : I₂) :
    σ c₂ c₁ c₁₂ i₂ i₁ = σ c₁ c₂ c₁₂ i₁ i₂ := by
  apply TotalComplexShapeSymmetrySymmetry.σ_symm
end ComplexShape