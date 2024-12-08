import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.OrderOfElement
section Defi
variable (R : Type*) [CommMonoid R]
variable (R' : Type*) [CommMonoidWithZero R']
structure MulChar extends MonoidHom R R' where
  map_nonunit' : ∀ a : R, ¬IsUnit a → toFun a = 0
instance MulChar.instFunLike : FunLike (MulChar R R') R R' :=
  ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩
class MulCharClass (F : Type*) (R R' : outParam Type*) [CommMonoid R]
  [CommMonoidWithZero R'] [FunLike F R R'] extends MonoidHomClass F R R' : Prop where
  map_nonunit : ∀ (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0
initialize_simps_projections MulChar (toFun → apply, -toMonoidHom)
end Defi
namespace MulChar
attribute [scoped simp] MulCharClass.map_nonunit
section Group
variable {R : Type*} [CommMonoid R]
variable {R' : Type*} [CommMonoidWithZero R']
variable (R R') in
@[simps]
noncomputable def trivial : MulChar R R' where
  toFun := by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto
@[simp]
theorem coe_mk (f : R →* R') (hf) : (MulChar.mk f hf : R → R') = f :=
  rfl
theorem ext' {χ χ' : MulChar R R'} (h : ∀ a, χ a = χ' a) : χ = χ' := by
  cases χ
  cases χ'
  congr
  exact MonoidHom.ext h
instance : MulCharClass (MulChar R R') R R' where
  map_mul χ := χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _
theorem map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0 :=
  χ.map_nonunit' a ha
@[ext]
theorem ext {χ χ' : MulChar R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' := by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]
def toUnitHom (χ : MulChar R R') : Rˣ →* R'ˣ :=
  Units.map χ
theorem coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a :=
  rfl
noncomputable def ofUnitHom (f : Rˣ →* R'ˣ) : MulChar R R' where
  toFun := by classical exact fun x => if hx : IsUnit x then f hx.unit else 0
  map_one' := by
    have h1 : (isUnit_one.unit : Rˣ) = 1 := Units.eq_iff.mp rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp only [hx, IsUnit.mul_iff, true_and, dif_pos]
        by_cases hy : IsUnit y
        · simp only [hy, dif_pos]
          have hm : (IsUnit.mul_iff.mpr ⟨hx, hy⟩).unit = hx.unit * hy.unit := Units.eq_iff.mp rfl
          rw [hm, map_mul]
          norm_cast
        · simp only [hy, not_false_iff, dif_neg, mul_zero]
      · simp only [hx, IsUnit.mul_iff, false_and, not_false_iff, dif_neg, zero_mul]
  map_nonunit' := by
    intro a ha
    simp only [ha, not_false_iff, dif_neg]
theorem ofUnitHom_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : ofUnitHom f ↑a = f a := by simp [ofUnitHom]
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ) where
  toFun := toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe, coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]
@[simp]
theorem toUnitHom_eq (χ : MulChar R R') : toUnitHom χ = equivToUnitHom χ :=
  rfl
@[simp]
theorem ofUnitHom_eq (χ : Rˣ →* R'ˣ) : ofUnitHom χ = equivToUnitHom.symm χ :=
  rfl
@[simp]
theorem coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equivToUnitHom χ a) = χ a :=
  coe_toUnitHom χ a
@[simp]
theorem equivToUnitHom_symm_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a :=
  ofUnitHom_coe f a
@[simp]
lemma coe_toMonoidHom (χ : MulChar R R')
    (x : R) : χ.toMonoidHom x = χ x := rfl
protected theorem map_one (χ : MulChar R R') : χ (1 : R) = 1 :=
  χ.map_one'
protected theorem map_zero {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    χ (0 : R) = 0 := by rw [map_nonunit χ not_isUnit_zero]
@[coe, simps]
def toMonoidWithZeroHom {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    R →*₀ R' where
  toFun := χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'
theorem map_ringChar {R : Type*} [CommRing R] [Nontrivial R] (χ : MulChar R R') :
    χ (ringChar R) = 0 := by rw [ringChar.Nat.cast_ringChar, χ.map_zero]
noncomputable instance hasOne : One (MulChar R R') :=
  ⟨trivial R R'⟩
noncomputable instance inhabited : Inhabited (MulChar R R') :=
  ⟨1⟩
@[simp]
theorem one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1 := by classical exact dif_pos a.isUnit
lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1 := one_apply_coe hx.unit
def mul (χ χ' : MulChar R R') : MulChar R R' :=
  { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }
instance hasMul : Mul (MulChar R R') :=
  ⟨mul⟩
theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
  rfl
@[simp]
theorem coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ' :=
  rfl
protected theorem one_mul (χ : MulChar R R') : (1 : MulChar R R') * χ = χ := by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
noncomputable def inv (χ : MulChar R R') : MulChar R R' :=
  { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }
noncomputable instance hasInv : Inv (MulChar R R') :=
  ⟨inv⟩
theorem inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = Ring.inverse (χ a) :=
  Eq.refl <| inv χ a
theorem inv_apply_eq_inv' {R' : Type*} [Field R'] (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ :=
  (inv_apply_eq_inv χ a).trans <| Ring.inverse_eq_inv (χ a)
theorem inv_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = χ (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h, ← map_mul, Ring.mul_inverse_cancel _ ha, map_one]
  · revert ha
    nontriviality R
    intro ha
    rw [map_nonunit _ ha, Ring.inverse_non_unit a ha, MulChar.map_zero χ]
theorem inv_apply' {R : Type*} [Field R] (χ : MulChar R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
  (inv_apply χ a).trans <| congr_arg _ (Ring.inverse_eq_inv a)
theorem inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1 := by
  ext x
  rw [coeToFun_mul, Pi.mul_apply, inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]
noncomputable instance commGroup : CommGroup (MulChar R R') :=
  { one := 1
    mul := (· * ·)
    inv := Inv.inv
    inv_mul_cancel := inv_mul
    mul_assoc := by
      intro χ₁ χ₂ χ₃
      ext a
      simp only [mul_assoc, Pi.mul_apply, MulChar.coeToFun_mul]
    mul_comm := by
      intro χ₁ χ₂
      ext a
      simp only [mul_comm, Pi.mul_apply, MulChar.coeToFun_mul]
    one_mul := MulChar.one_mul
    mul_one := MulChar.mul_one }
theorem pow_apply_coe (χ : MulChar R R') (n : ℕ) (a : Rˣ) : (χ ^ n) a = χ a ^ n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, one_apply_coe]
  · rw [pow_succ, pow_succ, mul_apply, ih]
theorem pow_apply' (χ : MulChar R R') {n : ℕ} (hn : n ≠ 0) (a : R) : (χ ^ n) a = χ a ^ n := by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]
lemma equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) :
    equivToUnitHom (χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a := by
  apply_fun ((↑) : R'ˣ → R') using Units.ext
  push_cast
  simp_rw [coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply]
noncomputable
def mulEquivToUnitHom : MulChar R R' ≃* (Rˣ →* R'ˣ) :=
  { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }
end Group
section Properties
section nontrivial
variable {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
lemma eq_one_iff {χ : MulChar R R'} : χ = 1 ↔ ∀ a : Rˣ, χ a = 1 := by
  simp only [MulChar.ext_iff, one_apply_coe]
lemma ne_one_iff {χ : MulChar R R'} : χ ≠ 1 ↔ ∃ a : Rˣ, χ a ≠ 1 := by
  simp only [Ne, eq_one_iff, not_forall]
@[deprecated "No deprecation message was provided." (since := "2024-06-16")]
def IsNontrivial (χ : MulChar R R') : Prop :=
  ∃ a : Rˣ, χ a ≠ 1
set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-06-16")]
theorem isNontrivial_iff (χ : MulChar R R') : χ.IsNontrivial ↔ χ ≠ 1 := by
  simp only [IsNontrivial, Ne, MulChar.ext_iff, not_forall, one_apply_coe]
end nontrivial
section quadratic_and_comp
variable {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*} [CommRing R'']
def IsQuadratic (χ : MulChar R R') : Prop :=
  ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1
theorem IsQuadratic.eq_of_eq_coe {χ : MulChar R ℤ} (hχ : IsQuadratic χ) {χ' : MulChar R' ℤ}
    (hχ' : IsQuadratic χ') [Nontrivial R''] (hR'' : ringChar R'' ≠ 2) {a : R} {a' : R'}
    (h : (χ a : R'') = χ' a') : χ a = χ' a' :=
  Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h
@[simps]
def ringHomComp (χ : MulChar R R') (f : R' →+* R'') : MulChar R R'' :=
  { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }
@[simp]
lemma ringHomComp_one (f : R' →+* R'') : (1 : MulChar R R').ringHomComp f = 1 := by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]
lemma ringHomComp_inv {R : Type*} [CommRing R] (χ : MulChar R R') (f : R' →+* R'') :
    (χ.ringHomComp f)⁻¹ = χ⁻¹.ringHomComp f := by
  ext1
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]
lemma ringHomComp_mul (χ φ : MulChar R R') (f : R' →+* R'') :
    (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f := by
  ext1
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]
lemma ringHomComp_pow (χ : MulChar R R') (f : R' →+* R'') (n : ℕ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  induction n with
  | zero => simp only [pow_zero, ringHomComp_one]
  | succ n ih => simp only [pow_succ, ih, ringHomComp_mul]
lemma injective_ringHomComp {f : R' →+* R''} (hf : Function.Injective f) :
    Function.Injective (ringHomComp (R := R) · f) := by
  simpa
    only [Function.Injective, MulChar.ext_iff, ringHomComp, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    using fun χ χ' h a ↦ hf (h a)
lemma ringHomComp_eq_one_iff {f : R' →+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f = 1 ↔ χ = 1 := by
  conv_lhs => rw [← (show (1 : MulChar R R').ringHomComp f = 1 by ext; simp)]
  exact (injective_ringHomComp hf).eq_iff
lemma ringHomComp_ne_one_iff {f : R' →+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f ≠ 1 ↔ χ ≠ 1 :=
  (ringHomComp_eq_one_iff hf).not
set_option linter.deprecated false in
@[deprecated ringHomComp_ne_one_iff (since := "2024-06-16")]
theorem IsNontrivial.comp {χ : MulChar R R'} (hχ : χ.IsNontrivial) {f : R' →+* R''}
    (hf : Function.Injective f) : (χ.ringHomComp f).IsNontrivial := by
  obtain ⟨a, ha⟩ := hχ
  use a
  simp_rw [ringHomComp_apply, ← RingHom.map_one f]
  exact fun h => ha (hf h)
theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' →+* R'') :
    (χ.ringHomComp f).IsQuadratic := by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]
theorem IsQuadratic.inv {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ⁻¹ = χ := by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · 
    have : (-1 : R') = (-1 : R'ˣ) := by rw [Units.val_neg, Units.val_one]
    rw [h₂, this, Ring.inverse_unit (-1 : R'ˣ)]
    rfl
theorem IsQuadratic.sq_eq_one {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ ^ 2 = 1 := by
  rw [← inv_mul_cancel χ, pow_two, hχ.inv]
theorem IsQuadratic.pow_char {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : ℕ) [hp : Fact p.Prime]
    [CharP R' p] : χ ^ p = χ := by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact neg_one_pow_char R' p
theorem IsQuadratic.pow_even {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Even n) :
    χ ^ n = 1 := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul, hχ.sq_eq_one, one_pow]
theorem IsQuadratic.pow_odd {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Odd n) :
    χ ^ n = χ := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add, pow_one, hχ.pow_even (even_two_mul _), one_mul]
lemma isQuadratic_iff_sq_eq_one {M R : Type*} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
    [Nontrivial R] {χ : MulChar M R} :
    IsQuadratic χ ↔ χ ^ 2 = 1:= by
  refine ⟨fun h ↦ ext (fun x ↦ ?_), fun h x ↦ ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit x
    · refine .inr <| sq_eq_one_iff.mp ?_
      rw [← χ.pow_apply' two_ne_zero, h, MulChar.one_apply hx]
    · exact .inl <| map_nonunit χ hx
end quadratic_and_comp
end Properties
section Finite
variable {M : Type*} [CommMonoid M]
variable {R : Type*} [CommMonoidWithZero R]
protected lemma pow_card_eq_one [Fintype Mˣ] (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
  ext1
  rw [pow_apply_coe, ← map_pow, one_apply_coe, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
    Units.val_eq_one.mpr rfl, map_one]
lemma orderOf_pos [Finite Mˣ] (χ : MulChar M R) : 0 < orderOf χ := by
  cases nonempty_fintype Mˣ
  apply IsOfFinOrder.orderOf_pos
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, χ.pow_card_eq_one⟩
end Finite
section sum
variable {R : Type*} [CommMonoid R] [Fintype R] {R' : Type*} [CommRing R']
theorem sum_eq_zero_of_ne_one [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) : ∑ a, χ a = 0 := by
  rcases ne_one_iff.mp hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul] using b.mulLeft_bijective.sum_comp _
set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-06-16")]
lemma IsNontrivial.sum_eq_zero [IsDomain R'] {χ : MulChar R R'} (hχ : χ.IsNontrivial) :
    ∑ a, χ a = 0 :=
  sum_eq_zero_of_ne_one ((isNontrivial_iff _).mp hχ)
theorem sum_one_eq_card_units [DecidableEq R] :
    (∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ := by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ → R), Units.ext⟩).card := ?_
    _ = Fintype.card Rˣ := congr_arg _ (Finset.card_map _)
  · split_ifs with h
    · exact one_apply_coe h.unit
    · exact map_nonunit _ h
  · congr
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_true_left, IsUnit]
end sum
section Ring
variable {R R' : Type*} [CommRing R] [CommMonoidWithZero R']
lemma val_neg_one_eq_one_of_odd_order {χ : MulChar R R'} {n : ℕ} (hn : Odd n) (hχ : χ ^ n = 1) :
    χ (-1) = 1 := by
  rw [← hn.neg_one_pow, map_pow, ← χ.pow_apply' (Nat.ne_of_odd_add hn), hχ]
  exact MulChar.one_apply_coe (-1)
end Ring
end MulChar