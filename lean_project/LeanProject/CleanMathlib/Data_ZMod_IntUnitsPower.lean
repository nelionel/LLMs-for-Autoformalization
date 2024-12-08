import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
instance : SMul (ZMod 2) (Additive ℤˣ) where
  smul z au := .ofMul <| au.toMul ^ z.val
lemma ZMod.smul_units_def (z : ZMod 2) (au : Additive ℤˣ) :
    z • au = z.val • au := rfl
lemma ZMod.natCast_smul_units (n : ℕ) (au : Additive ℤˣ) : (n : ZMod 2) • au = n • au :=
  (Int.units_pow_eq_pow_mod_two au n).symm
instance : Module (ZMod 2) (Additive ℤˣ) where
  smul z au := .ofMul <| au.toMul ^ z.val
  one_smul _ := Additive.toMul.injective <| pow_one _
  mul_smul z₁ z₂ au := Additive.toMul.injective <| by
    dsimp only [ZMod.smul_units_def, toMul_nsmul]
    rw [← pow_mul, ZMod.val_mul, ← Int.units_pow_eq_pow_mod_two, mul_comm]
  smul_zero _ := Additive.toMul.injective <| one_pow _
  smul_add _ _ _ := Additive.toMul.injective <| mul_pow _ _ _
  add_smul z₁ z₂ au := Additive.toMul.injective <| by
    dsimp only [ZMod.smul_units_def, toMul_nsmul, toMul_add]
    rw [← pow_add, ZMod.val_add, ← Int.units_pow_eq_pow_mod_two]
  zero_smul au := Additive.toMul.injective <| pow_zero au.toMul
section CommSemiring
variable {R : Type*} [CommSemiring R] [Module R (Additive ℤˣ)]
instance Int.instUnitsPow : Pow ℤˣ R where
  pow u r := (r • Additive.ofMul u).toMul
example : Int.instUnitsPow = Monoid.toNatPow := rfl
example : Int.instUnitsPow = DivInvMonoid.Pow := rfl
@[simp] lemma ofMul_uzpow (u : ℤˣ) (r : R) : Additive.ofMul (u ^ r) = r • Additive.ofMul u := rfl
@[simp] lemma toMul_uzpow (u : Additive ℤˣ) (r : R) :
  (r • u).toMul = u.toMul ^ r := rfl
@[norm_cast] lemma uzpow_natCast (u : ℤˣ) (n : ℕ) : u ^ (n : R) = u ^ n := by
  change ((n : R) • Additive.ofMul u).toMul = _
  rw [Nat.cast_smul_eq_nsmul, toMul_nsmul, toMul_ofMul]
lemma uzpow_coe_nat (s : ℤˣ) (n : ℕ) [n.AtLeastTwo] :
    s ^ (no_index (OfNat.ofNat n : R)) = s ^ (no_index (OfNat.ofNat n : ℕ)) :=
  uzpow_natCast _ _
@[simp] lemma one_uzpow (x : R) : (1 : ℤˣ) ^ x = 1 :=
  Additive.ofMul.injective <| smul_zero _
lemma mul_uzpow (s₁ s₂ : ℤˣ) (x : R) : (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x :=
  Additive.ofMul.injective <| smul_add x (Additive.ofMul s₁) (Additive.ofMul s₂)
@[simp] lemma uzpow_zero (s : ℤˣ) : (s ^ (0 : R) : ℤˣ) = (1 : ℤˣ) :=
  Additive.ofMul.injective <| zero_smul R (Additive.ofMul s)
@[simp] lemma uzpow_one (s : ℤˣ) : (s ^ (1 : R) : ℤˣ) = s :=
  Additive.ofMul.injective <| one_smul R (Additive.ofMul s)
lemma uzpow_mul (s : ℤˣ) (x y : R) : s ^ (x * y) = (s ^ x) ^ y :=
  Additive.ofMul.injective <| mul_comm x y ▸ mul_smul y x (Additive.ofMul s)
lemma uzpow_add (s : ℤˣ) (x y : R) : s ^ (x + y) = s ^ x * s ^ y :=
  Additive.ofMul.injective <| add_smul x y (Additive.ofMul s)
end CommSemiring
section CommRing
variable {R : Type*} [CommRing R] [Module R (Additive ℤˣ)]
lemma uzpow_sub (s : ℤˣ) (x y : R) : s ^ (x - y) = s ^ x / s ^ y :=
  Additive.ofMul.injective <| sub_smul x y (Additive.ofMul s)
lemma uzpow_neg (s : ℤˣ) (x : R) : s ^ (-x) = (s ^ x)⁻¹ :=
  Additive.ofMul.injective <| neg_smul x (Additive.ofMul s)
@[norm_cast] lemma uzpow_intCast (u : ℤˣ) (z : ℤ) : u ^ (z : R) = u ^ z := by
  change ((z : R) • Additive.ofMul u).toMul = _
  rw [Int.cast_smul_eq_zsmul, toMul_zsmul, toMul_ofMul]
end CommRing