import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.MulChar.Basic
abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R
open MulChar
variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)
namespace DirichletCharacter
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.unit := by simp
lemma toUnitHom_eq_iff (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp
lemma eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x) := by simp
noncomputable def changeLevel {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m where
  toFun ψ := MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp
lemma changeLevel_def {m : ℕ} (hm : n ∣ m) :
    changeLevel hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl
lemma changeLevel_toUnitHom {m : ℕ} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  simp [changeLevel]
lemma changeLevel_injective {m : ℕ} [NeZero m] (hm : n ∣ m) :
    Function.Injective (changeLevel (R := R) hm) := by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z
@[simp]
lemma changeLevel_eq_one_iff {m : ℕ} {χ : DirichletCharacter R n} (hm : n ∣ m) [NeZero m] :
    changeLevel hm χ = 1 ↔ χ = 1 :=
  map_eq_one_iff _ (changeLevel_injective hm)
@[simp]
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  simp [changeLevel, ZMod.unitsMap]
lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]
lemma changeLevel_trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
lemma changeLevel_eq_cast_of_dvd {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ (ZMod.cast (a : ZMod m)) := by
  set_option tactic.skipAssignedInstances false in
  simpa [changeLevel_def, Function.comp_apply, MonoidHom.coe_comp] using
      toUnitHom_eq_char' _ <| ZMod.IsUnit_cast_of_dvd hm a
def FactorsThrough (d : ℕ) : Prop :=
  ∃ (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀
lemma changeLevel_factorsThrough {m : ℕ} (hm : n ∣ m) : FactorsThrough (changeLevel hm χ) n :=
  ⟨hm, χ, rfl⟩
namespace FactorsThrough
variable {χ}
lemma dvd {d : ℕ} (h : FactorsThrough χ d) : d ∣ n := h.1
noncomputable
def χ₀ {d : ℕ} (h : FactorsThrough χ d) : DirichletCharacter R d := Classical.choose h.2
lemma eq_changeLevel {d : ℕ} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀ :=
  Classical.choose_spec h.2
lemma existsUnique {d : ℕ} [NeZero n] (h : FactorsThrough χ d) :
    ∃! χ' : DirichletCharacter R d, χ = changeLevel h.dvd χ' := by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ ↦ (changeLevel_injective hd hχ₃).symm⟩
variable (χ) in
lemma same_level : FactorsThrough χ n := ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩
end FactorsThrough
variable {χ} in
lemma factorsThrough_iff_ker_unitsMap {d : ℕ} [NeZero n] (hd : d ∣ n) :
    FactorsThrough χ d ↔ (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker := by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
    refine ⟨hd, MulChar.ofUnitHom E, equivToUnitHom.injective (?_ : toUnitHom _ = toUnitHom _)⟩
    simp_rw [changeLevel_toUnitHom, toUnitHom_eq, ofUnitHom_eq, Equiv.apply_symm_apply, hE,
      toUnitHom_eq]
lemma level_one (χ : DirichletCharacter R 1) : χ = 1 := by
  ext
  simp [units_eq_one]
lemma level_one' (hn : n = 1) : χ = 1 := by
  subst hn
  exact level_one _
instance : Subsingleton (DirichletCharacter R 1) := by
  refine subsingleton_iff.mpr (fun χ χ' ↦ ?_)
  simp [level_one]
noncomputable instance : Unique (DirichletCharacter R 1) := Unique.mk' (DirichletCharacter R 1)
lemma map_zero' (hn : n ≠ 1) : χ 0 = 0 :=
  have := ZMod.nontrivial_iff.mpr hn; χ.map_zero
lemma changeLevel_one {d : ℕ} (h : d ∣ n) :
    changeLevel h (1 : DirichletCharacter R d) = 1 := by
  simp
lemma factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1 := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ ↦ ?_,
          fun h ↦ ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀
def conductorSet : Set ℕ := {d : ℕ | FactorsThrough χ d}
lemma mem_conductorSet_iff {x : ℕ} : x ∈ conductorSet χ ↔ FactorsThrough χ x := Iff.refl _
lemma level_mem_conductorSet : n ∈ conductorSet χ := FactorsThrough.same_level χ
lemma mem_conductorSet_dvd {x : ℕ} (hx : x ∈ conductorSet χ) : x ∣ n := hx.dvd
noncomputable def conductor : ℕ := sInf (conductorSet χ)
lemma conductor_mem_conductorSet : conductor χ ∈ conductorSet χ :=
  Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))
lemma conductor_dvd_level : conductor χ ∣ n := (conductor_mem_conductorSet χ).dvd
lemma factorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ
lemma conductor_ne_zero (hn : n ≠ 0) : conductor χ ≠ 0 :=
  fun h ↦ hn <| Nat.eq_zero_of_zero_dvd <| h ▸ conductor_dvd_level _
lemma conductor_one (hn : n ≠ 0) : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) ≤ 1 :=
      Nat.sInf_le <| (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _ hn)
  exact (factorsThrough_one_iff _).mpr rfl
variable {χ}
lemma eq_one_iff_conductor_eq_one (hn : n ≠ 0) : χ = 1 ↔ conductor χ = 1 := by
  refine ⟨fun h ↦ h ▸ conductor_one hn, fun hχ ↦ ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
  exact (level_one' χ₀ hχ ▸ h).trans <| changeLevel_one h'
lemma conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0 := by
  refine ⟨(conductor_ne_zero χ).mtr, ?_⟩
  rintro rfl
  exact Nat.sInf_eq_zero.mpr <| Or.inl <| level_mem_conductorSet χ
lemma conductor_le_conductor_mem_conductorSet {d : ℕ} (hd : d ∈ conductorSet χ) :
    χ.conductor ≤ (Classical.choose hd.2).conductor := by
  refine Nat.sInf_le <| (mem_conductorSet_iff χ).mpr <|
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd,
      ← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact hd.eq_changeLevel
variable (χ)
def IsPrimitive : Prop := conductor χ = n
@[deprecated (since := "2024-06-16")] alias isPrimitive := IsPrimitive
lemma isPrimitive_def : IsPrimitive χ ↔ conductor χ = n := Iff.rfl
lemma isPrimitive_one_level_one : IsPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)
lemma isPritive_one_level_zero : IsPrimitive (1 : DirichletCharacter R 0) :=
  conductor_eq_zero_iff_level_eq_zero.mpr rfl
lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec
lemma primitiveCharacter_isPrimitive : IsPrimitive (χ.primitiveCharacter) := by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert conductor_eq_zero_iff_level_eq_zero.mpr h
  · exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _)) <|
      conductor_le_conductor_mem_conductorSet <| conductor_mem_conductorSet χ
lemma primitiveCharacter_one (hn : n ≠ 0) :
    (1 : DirichletCharacter R n).primitiveCharacter = 1 := by
  rw [eq_one_iff_conductor_eq_one <| (@conductor_one R _ _ hn) ▸ Nat.one_ne_zero,
      (isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive,
      conductor_one hn]
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
    DirichletCharacter R (Nat.lcm n m) :=
  changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂
noncomputable def primitive_mul {m : ℕ} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor :=
  primitiveCharacter (mul χ₁ χ₂)
lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.primitive_mul ψ = primitiveCharacter (mul χ ψ) :=
  rfl
lemma primitive_mul_isPrimitive {m : ℕ} (ψ : DirichletCharacter R m) :
    IsPrimitive (primitive_mul χ ψ) :=
  primitiveCharacter_isPrimitive _
@[deprecated (since := "2024-06-16")] alias isPrimitive.primitive_mul := primitive_mul_isPrimitive
section CommRing
variable {S : Type*} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)
def Odd : Prop := ψ (-1) = -1
def Even : Prop := ψ (-1) = 1
lemma even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd := by
  suffices ψ (-1) ^ 2 = 1 by convert sq_eq_one_iff.mp this
  rw [← map_pow _, neg_one_sq, map_one]
lemma not_even_and_odd [NeZero (2 : S)] : ¬(ψ.Even ∧ ψ.Odd) := by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h
lemma Even.not_odd [NeZero (2 : S)] (hψ : Even ψ) : ¬Odd ψ :=
  not_and.mp ψ.not_even_and_odd hψ
lemma Odd.not_even [NeZero (2 : S)] (hψ : Odd ψ) : ¬Even ψ :=
  not_and'.mp ψ.not_even_and_odd hψ
lemma Odd.toUnitHom_eval_neg_one (hψ : ψ.Odd) : ψ.toUnitHom (-1) = -1 := by
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  exact hψ
lemma Even.toUnitHom_eval_neg_one (hψ : ψ.Even) : ψ.toUnitHom (-1) = 1 := by
  rw [← Units.eq_iff, MulChar.coe_toUnitHom]
  exact hψ
lemma Odd.eval_neg (x : ZMod m) (hψ : ψ.Odd) : ψ (- x) = - ψ x := by
  rw [Odd] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]
lemma Even.eval_neg (x : ZMod m) (hψ : ψ.Even) : ψ (- x) = ψ x := by
  rw [Even] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]
lemma Even.to_fun {χ : DirichletCharacter S m} (hχ : Even χ) : Function.Even χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, one_mul]
lemma Odd.to_fun {χ : DirichletCharacter S m} (hχ : Odd χ) : Function.Odd χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]
end CommRing
end DirichletCharacter