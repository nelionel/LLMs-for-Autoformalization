import Mathlib.Logic.Small.Defs
import Mathlib.Logic.Equiv.TransferInstance
noncomputable section
variable {α : Type*}
@[to_additive]
noncomputable instance [One α] [Small α] : One (Shrink α) := (equivShrink _).symm.one
@[to_additive (attr := simp)]
lemma equivShrink_symm_one [One α] [Small α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1
@[to_additive]
noncomputable instance [Mul α] [Small α] : Mul (Shrink α) := (equivShrink _).symm.mul
@[to_additive (attr := simp)]
lemma equivShrink_symm_mul [Mul α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  rw [Equiv.mul_def]
  simp
@[to_additive (attr := simp)]
lemma equivShrink_mul [Mul α] [Small α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  rw [Equiv.mul_def]
  simp
@[simp]
lemma equivShrink_symm_smul {R : Type*} [SMul R α] [Small α] (r : R) (x : Shrink α) :
    (equivShrink α).symm (r • x) = r • (equivShrink α).symm x := by
  rw [Equiv.smul_def]
  simp
@[simp]
lemma equivShrink_smul {R : Type*} [SMul R α] [Small α] (r : R) (x : α) :
    equivShrink α (r • x) = r • equivShrink α x := by
  rw [Equiv.smul_def]
  simp
@[to_additive]
noncomputable instance [Div α] [Small α] : Div (Shrink α) := (equivShrink _).symm.div
@[to_additive (attr := simp)]
lemma equivShrink_symm_div [Div α] [Small α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  rw [Equiv.div_def]
  simp
@[to_additive (attr := simp)]
lemma equivShrink_div [Div α] [Small α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  rw [Equiv.div_def]
  simp
@[to_additive]
noncomputable instance [Inv α] [Small α] : Inv (Shrink α) := (equivShrink _).symm.Inv
@[to_additive (attr := simp)]
lemma equivShrink_symm_inv [Inv α] [Small α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  rw [Equiv.inv_def]
  simp
@[to_additive (attr := simp)]
lemma equivShrink_inv [Inv α] [Small α] (x : α) :
    equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  rw [Equiv.inv_def]
  simp
@[to_additive]
noncomputable instance [Semigroup α] [Small α] : Semigroup (Shrink α) :=
  (equivShrink _).symm.semigroup
instance [SemigroupWithZero α] [Small α] : SemigroupWithZero (Shrink α) :=
  (equivShrink _).symm.semigroupWithZero
@[to_additive]
noncomputable instance [CommSemigroup α] [Small α] : CommSemigroup (Shrink α) :=
  (equivShrink _).symm.commSemigroup
instance [MulZeroClass α] [Small α] : MulZeroClass (Shrink α) :=
  (equivShrink _).symm.mulZeroClass
@[to_additive]
noncomputable instance [MulOneClass α] [Small α] : MulOneClass (Shrink α) :=
  (equivShrink _).symm.mulOneClass
instance [MulZeroOneClass α] [Small α] : MulZeroOneClass (Shrink α) :=
  (equivShrink _).symm.mulZeroOneClass
@[to_additive]
noncomputable instance [Monoid α] [Small α] : Monoid (Shrink α) :=
  (equivShrink _).symm.monoid
@[to_additive]
noncomputable instance [CommMonoid α] [Small α] : CommMonoid (Shrink α) :=
  (equivShrink _).symm.commMonoid
@[to_additive]
noncomputable instance [Group α] [Small α] : Group (Shrink α) :=
  (equivShrink _).symm.group
@[to_additive]
noncomputable instance [CommGroup α] [Small α] : CommGroup (Shrink α) :=
  (equivShrink _).symm.commGroup