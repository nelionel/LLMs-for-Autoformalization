import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Iterate
import Mathlib.Order.SemiconjSup
import Mathlib.Topology.Order.MonotoneContinuity
open Filter Set Int Topology
open Function hiding Commute
structure CircleDeg1Lift extends ℝ →o ℝ : Type where
  map_add_one' : ∀ x, toFun (x + 1) = toFun x + 1
namespace CircleDeg1Lift
instance : FunLike CircleDeg1Lift ℝ ℝ where
  coe f := f.toFun
  coe_injective' | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl
instance : OrderHomClass CircleDeg1Lift ℝ ℝ where
  map_rel f _ _ h := f.monotone' h
@[simp] theorem coe_mk (f h) : ⇑(mk f h) = f := rfl
variable (f g : CircleDeg1Lift)
@[simp] theorem coe_toOrderHom : ⇑f.toOrderHom = f := rfl
protected theorem monotone : Monotone f := f.monotone'
@[mono] theorem mono {x y} (h : x ≤ y) : f x ≤ f y := f.monotone h
theorem strictMono_iff_injective : StrictMono f ↔ Injective f :=
  f.monotone.strictMono_iff_injective
@[simp]
theorem map_add_one : ∀ x, f (x + 1) = f x + 1 :=
  f.map_add_one'
@[simp]
theorem map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm 1]
@[ext]
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
instance : Monoid CircleDeg1Lift where
  mul f g :=
    { toOrderHom := f.1.comp g.1
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨.id, fun _ => rfl⟩
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := DFunLike.coe_injective rfl
instance : Inhabited CircleDeg1Lift := ⟨1⟩
@[simp]
theorem coe_mul : ⇑(f * g) = f ∘ g :=
  rfl
theorem mul_apply (x) : (f * g) x = f (g x) :=
  rfl
@[simp]
theorem coe_one : ⇑(1 : CircleDeg1Lift) = id :=
  rfl
instance unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => ℝ → ℝ :=
  ⟨fun f => ⇑(f : CircleDeg1Lift)⟩
@[simp]
theorem units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : ℝ) :
    (f⁻¹ : CircleDeg1Liftˣ) (f x) = x := by simp only [← mul_apply, f.inv_mul, coe_one, id]
@[simp]
theorem units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : ℝ) :
    f ((f⁻¹ : CircleDeg1Liftˣ) x) = x := by simp only [← mul_apply, f.mul_inv, coe_one, id]
def toOrderIso : CircleDeg1Liftˣ →* ℝ ≃o ℝ where
  toFun f :=
    { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl
@[simp]
theorem coe_toOrderIso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f :=
  rfl
@[simp]
theorem coe_toOrderIso_symm (f : CircleDeg1Liftˣ) :
    ⇑(toOrderIso f).symm = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
@[simp]
theorem coe_toOrderIso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
theorem isUnit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strictMono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
              h.1 <| by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
        val_inv := ext <| Equiv.ofBijective_apply_symm_apply f h
        inv_val := ext <| Equiv.ofBijective_symm_apply_apply f h }⟩
theorem coe_pow : ∀ n : ℕ, ⇑(f ^ n) = f^[n]
  | 0 => rfl
  | n + 1 => by
    ext x
    simp [coe_pow n, pow_succ]
theorem semiconjBy_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} :
    SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂ :=
  CircleDeg1Lift.ext_iff
theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  CircleDeg1Lift.ext_iff
def translate : Multiplicative ℝ →* CircleDeg1Liftˣ := MonoidHom.toHomUnits <|
  { toFun := fun x =>
      ⟨⟨fun y => x.toAdd + y, fun _ _ h => add_le_add_left h _⟩, fun _ =>
        (add_assoc _ _ _).symm⟩
    map_one' := ext <| zero_add
    map_mul' := fun _ _ => ext <| add_assoc _ _ }
@[simp]
theorem translate_apply (x y : ℝ) : translate (Multiplicative.ofAdd x) y = x + y :=
  rfl
@[simp]
theorem translate_inv_apply (x y : ℝ) : (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y :=
  rfl
@[simp]
theorem translate_zpow (x : ℝ) (n : ℤ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) := by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, MonoidHom.map_zpow]
@[simp]
theorem translate_pow (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n
@[simp]
theorem translate_iterate (x : ℝ) (n : ℕ) :
    (translate (Multiplicative.ofAdd x))^[n] = translate (Multiplicative.ofAdd <| ↑n * x) := by
  rw [← coe_pow, ← Units.val_pow_eq_pow_val, translate_pow]
theorem commute_nat_add (n : ℕ) : Function.Commute f (n + ·) := by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n
theorem commute_add_nat (n : ℕ) : Function.Commute f (· + n) := by
  simp only [add_comm _ (n : ℝ), f.commute_nat_add n]
theorem commute_sub_nat (n : ℕ) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
theorem commute_add_int : ∀ n : ℤ, Function.Commute f (· + n)
  | (n : ℕ) => f.commute_add_nat n
  | -[n+1] => by simpa [sub_eq_add_neg] using f.commute_sub_nat (n + 1)
theorem commute_int_add (n : ℤ) : Function.Commute f (n + ·) := by
  simpa only [add_comm _ (n : ℝ)] using f.commute_add_int n
theorem commute_sub_int (n : ℤ) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
@[simp]
theorem map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
  f.commute_int_add m x
@[simp]
theorem map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
  f.commute_add_int m x
@[simp]
theorem map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
  f.commute_sub_int n x
@[simp]
theorem map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
  f.map_add_int x n
@[simp]
theorem map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
  f.map_int_add n x
@[simp]
theorem map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
  f.map_sub_int x n
theorem map_int_of_map_zero (n : ℤ) : f n = f 0 + n := by rw [← f.map_add_int, zero_add]
@[simp]
theorem map_fract_sub_fract_eq (x : ℝ) : f (fract x) - fract x = f x - x := by
  rw [Int.fract, f.map_sub_int, sub_sub_sub_cancel_right]
noncomputable instance : Lattice CircleDeg1Lift where
  sup f g :=
    { toFun := fun x => max (f x) (g x)
      monotone' := fun _ _ h => max_le_max (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_refl (f x)
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
  le_sup_left f g x := le_max_left (f x) (g x)
  le_sup_right f g x := le_max_right (f x) (g x)
  sup_le _ _ _ h₁ h₂ x := max_le (h₁ x) (h₂ x)
  inf f g :=
    { toFun := fun x => min (f x) (g x)
      monotone' := fun _ _ h => min_le_min (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [min_add_add_right] }
  inf_le_left f g x := min_le_left (f x) (g x)
  inf_le_right f g x := min_le_right (f x) (g x)
  le_inf _ _ _ h₂ h₃ x := le_min (h₂ x) (h₃ x)
@[simp]
theorem sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) :=
  rfl
@[simp]
theorem inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) :=
  rfl
theorem iterate_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f^[n] := fun f _ h =>
  f.monotone.iterate_le_of_le h _
theorem iterate_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  iterate_monotone n h
theorem pow_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n := fun x => by
  simp only [coe_pow, iterate_mono h n x]
theorem pow_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f ^ n := fun _ _ h => pow_mono h n
theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
  calc
    f x ≤ f ⌈x⌉ := f.monotone <| le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _
theorem map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)
theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
    ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ := floor_mono <| f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_int _ _
theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
    ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono <| f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_int _ _
theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := add_lt_add_left (ceil_lt_add_one _) _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm
theorem le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
    _ ≤ f x := f.monotone <| floor_le _
theorem le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)
theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_int _ _).symm
    _ ≤ ⌊f (g 0)⌋ := floor_mono <| f.le_map_map_zero g
theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_int _ _).symm
    _ ≤ ⌈f (g 0)⌉ := ceil_mono <| f.le_map_map_zero g
theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := add_lt_add_left (sub_one_lt_floor _) _
    _ ≤ f (g 0) := f.le_map_map_zero g
theorem dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 := by
  rw [dist_comm, Real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  calc
    dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 1 + 1 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    _ = 2 := one_add_one_eq_two
theorem dist_map_zero_lt_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  dist_map_zero_lt_of_semiconj <| semiconjBy_iff_semiconj.1 h
protected theorem tendsto_atBot : Tendsto f atBot atBot :=
  tendsto_atBot_mono f.map_le_of_map_zero <| tendsto_atBot_add_const_left _ _ <|
    (tendsto_atBot_mono fun x => (ceil_lt_add_one x).le) <|
      tendsto_atBot_add_const_right _ _ tendsto_id
protected theorem tendsto_atTop : Tendsto f atTop atTop :=
  tendsto_atTop_mono f.le_map_of_map_zero <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) <| by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ _ tendsto_id
theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.surjective f.tendsto_atTop f.tendsto_atBot, f.monotone.continuous_of_surjective⟩
theorem iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) (n : ℕ) :
    f^[n] x ≤ x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const (m : ℝ)) h n
theorem le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : x + m ≤ f x) (n : ℕ) :
    x + n * m ≤ f^[n] x := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const (m : ℝ)) f.monotone h n
theorem iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
    f^[n] x = x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h
theorem iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x ≤ x + n * m ↔ f x ≤ x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strictMono_id.add_const (m : ℝ)) hn
theorem iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x < x + n * m ↔ f x < x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strictMono_id.add_const (m : ℝ)) hn
theorem iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x = x + n * m ↔ f x = x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strictMono_id.add_const (m : ℝ)) hn
theorem le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m ≤ f^[n] x ↔ x + m ≤ f x := by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)
theorem lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m < f^[n] x ↔ x + m < f x := by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)
theorem mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊f^[n] 0⌋ := by
  rw [le_floor, Int.cast_mul, Int.cast_natCast, ← zero_add ((n : ℝ) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]
noncomputable section
def transnumAuxSeq (n : ℕ) : ℝ :=
  (f ^ (2 ^ n : ℕ)) 0 / 2 ^ n
def translationNumber : ℝ :=
  limUnder atTop f.transnumAuxSeq
end
local notation "τ" => translationNumber
theorem transnumAuxSeq_def : f.transnumAuxSeq = fun n : ℕ => (f ^ (2 ^ n : ℕ)) 0 / 2 ^ n :=
  rfl
theorem translationNumber_eq_of_tendsto_aux {τ' : ℝ} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')) :
    τ f = τ' :=
  h.limUnder_eq
theorem translationNumber_eq_of_tendsto₀ {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => f^[n] 0 / n) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto_aux <| by
    simpa [Function.comp_def, transnumAuxSeq_def, coe_pow] using
      h.comp (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
theorem translationNumber_eq_of_tendsto₀' {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => f^[n + 1] 0 / (n + 1)) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto₀ <| (tendsto_add_atTop_iff_nat 1).1 (mod_cast h)
theorem transnumAuxSeq_zero : f.transnumAuxSeq 0 = f 0 := by simp [transnumAuxSeq]
theorem transnumAuxSeq_dist_lt (n : ℕ) :
    dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n := by
  have : 0 < (2 ^ (n + 1) : ℝ) := pow_pos zero_lt_two _
  rw [div_div, ← pow_succ', ← abs_of_pos this]
  calc
    _ = dist ((f ^ 2 ^ n) 0 + (f ^ 2 ^ n) 0) ((f ^ 2 ^ n) ((f ^ 2 ^ n) 0)) / |2 ^ (n + 1)| := by
      simp_rw [transnumAuxSeq, Real.dist_eq]
      rw [← abs_div, sub_div, pow_succ, pow_succ', ← two_mul, mul_div_mul_left _ _ (two_ne_zero' ℝ),
        pow_mul, sq, mul_apply]
    _ < _ := by gcongr; exact (f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n)
theorem tendsto_translationNumber_aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f) :=
  (cauchySeq_of_le_geometric_two fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder
theorem dist_map_zero_translationNumber_le : dist (f 0) (τ f) ≤ 1 :=
  f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux
theorem tendsto_translationNumber_of_dist_bounded_aux (x : ℕ → ℝ) (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) (x n) ≤ C) :
    Tendsto (fun n : ℕ => x (2 ^ n) / 2 ^ n) atTop (𝓝 <| τ f) := by
  apply f.tendsto_translationNumber_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : ℝ) := pow_pos zero_lt_two _
    convert (div_le_div_iff_of_pos_right this).2 (H (2 ^ n)) using 1
    rw [transnumAuxSeq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos this, Real.dist_eq]
  · exact mul_zero C ▸ tendsto_const_nhds.mul <| tendsto_inv_atTop_zero.comp <|
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
theorem translationNumber_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) ((g ^ n) 0) ≤ C) : τ f = τ g :=
  Eq.symm <| g.translationNumber_eq_of_tendsto_aux <|
    f.tendsto_translationNumber_of_dist_bounded_aux (fun n ↦ (g ^ n) 0) C H
@[simp]
theorem translationNumber_one : τ 1 = 0 :=
  translationNumber_eq_of_tendsto₀ _ <| by simp [tendsto_const_nhds]
theorem translationNumber_eq_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) :
    τ g₁ = τ g₂ :=
  translationNumber_eq_of_dist_bounded 2 fun n =>
    le_of_lt <| dist_map_zero_lt_of_semiconjBy <| H.pow_right n
theorem translationNumber_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift}
    (H : Function.Semiconj f g₁ g₂) : τ g₁ = τ g₂ :=
  translationNumber_eq_of_semiconjBy <| semiconjBy_iff_semiconj.2 H
theorem translationNumber_mul_of_commute {f g : CircleDeg1Lift} (h : Commute f g) :
    τ (f * g) = τ f + τ g := by
  refine tendsto_nhds_unique ?_
    (f.tendsto_translationNumber_aux.add g.tendsto_translationNumber_aux)
  simp only [transnumAuxSeq, ← add_div]
  refine (f * g).tendsto_translationNumber_of_dist_bounded_aux
    (fun n ↦ (f ^ n) 0 + (g ^ n) 0) 1 fun n ↦ ?_
  rw [h.mul_pow, dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))
@[simp]
theorem translationNumber_units_inv (f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f :=
  eq_neg_iff_add_eq_zero.2 <| by
    simp [← translationNumber_mul_of_commute (Commute.refl _).units_inv_left]
@[simp]
theorem translationNumber_pow : ∀ n : ℕ, τ (f ^ n) = n * τ f
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, translationNumber_mul_of_commute (Commute.pow_self f n),
      translationNumber_pow n, Nat.cast_add_one, add_mul, one_mul]
@[simp]
theorem translationNumber_zpow (f : CircleDeg1Liftˣ) : ∀ n : ℤ, τ (f ^ n : Units _) = n * τ f
  | (n : ℕ) => by simp [translationNumber_pow f n]
  | -[n+1] => by simp; ring
@[simp]
theorem translationNumber_conj_eq (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f * g * ↑f⁻¹) = τ g :=
  (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm
@[simp]
theorem translationNumber_conj_eq' (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f⁻¹ * g * f) = τ g :=
  translationNumber_conj_eq f⁻¹ g
theorem dist_pow_map_zero_mul_translationNumber_le (n : ℕ) :
    dist ((f ^ n) 0) (n * f.translationNumber) ≤ 1 :=
  f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le
theorem tendsto_translation_number₀' :
    Tendsto (fun n : ℕ => (f ^ (n + 1) : CircleDeg1Lift) 0 / ((n : ℝ) + 1)) atTop (𝓝 <| τ f) := by
  refine
    tendsto_iff_dist_tendsto_zero.2 <|
      squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        ((tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1))
  dsimp
  have : (0 : ℝ) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq, div_sub' _ _ _ (ne_of_gt this), abs_div, ← Real.dist_eq, abs_of_pos this,
    Nat.cast_add_one, div_le_div_iff_of_pos_right this, ← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translationNumber_le
theorem tendsto_translation_number₀ : Tendsto (fun n : ℕ => (f ^ n) 0 / n) atTop (𝓝 <| τ f) :=
  (tendsto_add_atTop_iff_nat 1).1 (mod_cast f.tendsto_translation_number₀')
theorem tendsto_translationNumber (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ n) x - x) / n) atTop (𝓝 <| τ f) := by
  rw [← translationNumber_conj_eq' (translate <| Multiplicative.ofAdd x)]
  refine (tendsto_translation_number₀ _).congr fun n ↦ ?_
  simp [sub_eq_neg_add, Units.conj_pow']
theorem tendsto_translation_number' (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ (n + 1) : CircleDeg1Lift) x - x) / (n + 1)) atTop (𝓝 <| τ f) :=
  mod_cast (tendsto_add_atTop_iff_nat 1).2 (f.tendsto_translationNumber x)
theorem translationNumber_mono : Monotone τ := fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n => by
    gcongr; exact pow_mono h _ _
theorem translationNumber_translate (x : ℝ) : τ (translate <| Multiplicative.ofAdd x) = x :=
  translationNumber_eq_of_tendsto₀' _ <| by
    simp only [translate_iterate, translate_apply, add_zero, Nat.cast_succ,
      mul_div_cancel_left₀ (M₀ := ℝ) _ (Nat.cast_add_one_ne_zero _), tendsto_const_nhds]
theorem translationNumber_le_of_le_add {z : ℝ} (hz : ∀ x, f x ≤ x + z) : τ f ≤ z :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (hz x).trans_eq (add_comm _ _)
theorem le_translationNumber_of_add_le {z : ℝ} (hz : ∀ x, x + z ≤ f x) : z ≤ τ f :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (add_comm _ _).trans_le (hz x)
theorem translationNumber_le_of_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) : τ f ≤ m :=
  le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (div_le_iff₀' (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <| sub_le_iff_le_add'.2 <|
      (coe_pow f (n + 1)).symm ▸ @Nat.cast_add_one ℝ _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)
theorem translationNumber_le_of_le_add_nat {x : ℝ} {m : ℕ} (h : f x ≤ x + m) : τ f ≤ m :=
  @translationNumber_le_of_le_add_int f x m h
theorem le_translationNumber_of_add_int_le {x : ℝ} {m : ℤ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (le_div_iff₀ (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <| le_sub_iff_add_le'.2 <| by
      simp only [coe_pow, mul_comm (m : ℝ), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]
theorem le_translationNumber_of_add_nat_le {x : ℝ} {m : ℕ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  @le_translationNumber_of_add_int_le f x m h
theorem translationNumber_of_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) : τ f = m :=
  le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)
theorem floor_sub_le_translationNumber (x : ℝ) : ↑⌊f x - x⌋ ≤ τ f :=
  le_translationNumber_of_add_int_le f <| le_sub_iff_add_le'.1 (floor_le <| f x - x)
theorem translationNumber_le_ceil_sub (x : ℝ) : τ f ≤ ⌈f x - x⌉ :=
  translationNumber_le_of_le_add_int f <| sub_le_iff_le_add'.1 (le_ceil <| f x - x)
theorem map_lt_of_translationNumber_lt_int {n : ℤ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  not_le.1 <| mt f.le_translationNumber_of_add_int_le <| not_le.2 h
theorem map_lt_of_translationNumber_lt_nat {n : ℕ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  @map_lt_of_translationNumber_lt_int f n h x
theorem map_lt_add_floor_translationNumber_add_one (x : ℝ) : f x < x + ⌊τ f⌋ + 1 := by
  rw [add_assoc]
  norm_cast
  refine map_lt_of_translationNumber_lt_int _ ?_ _
  push_cast
  exact lt_floor_add_one _
theorem map_lt_add_translationNumber_add_one (x : ℝ) : f x < x + τ f + 1 :=
  calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ ≤ x + τ f + 1 := by gcongr; apply floor_le
theorem lt_map_of_int_lt_translationNumber {n : ℤ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  not_le.1 <| mt f.translationNumber_le_of_le_add_int <| not_le.2 h
theorem lt_map_of_nat_lt_translationNumber {n : ℕ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  @lt_map_of_int_lt_translationNumber f n h x
theorem translationNumber_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ} (h : (f ^ n) x = x + m)
    (hn : 0 < n) : τ f = m / n := by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translationNumber_pow, mul_comm, ← eq_div_iff] at this
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)
theorem forall_map_sub_of_Icc (P : ℝ → Prop) (h : ∀ x ∈ Icc (0 : ℝ) 1, P (f x - x)) (x : ℝ) :
    P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩
theorem translationNumber_lt_of_forall_lt_add (hf : Continuous f) {z : ℝ} (hz : ∀ x, f x < x + z) :
    τ f < z := by
  obtain ⟨x, -, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f y - y ≤ f x - x :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuousOn
  refine lt_of_le_of_lt ?_ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translationNumber_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a ≤ f x - x) hx
theorem lt_translationNumber_of_forall_add_lt (hf : Continuous f) {z : ℝ} (hz : ∀ x, x + z < f x) :
    z < τ f := by
  obtain ⟨x, -, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x - x ≤ f y - y :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).continuousOn
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) ?_
  apply le_translationNumber_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx
theorem exists_eq_add_translationNumber (hf : Continuous f) : ∃ x, f x = x + τ f := by
  obtain ⟨a, ha⟩ : ∃ x, f x ≤ x + τ f := by
    by_contra! H
    exact lt_irrefl _ (f.lt_translationNumber_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : ∃ x, x + τ f ≤ f x := by
    by_contra! H
    exact lt_irrefl _ (f.translationNumber_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (continuous_id.add continuous_const) ha hb
theorem translationNumber_eq_int_iff (hf : Continuous f) {m : ℤ} :
    τ f = m ↔ ∃ x : ℝ, f x = x + m := by
  constructor
  · intro h
    simp only [← h]
    exact f.exists_eq_add_translationNumber hf
  · rintro ⟨x, hx⟩
    exact f.translationNumber_of_eq_add_int hx
theorem continuous_pow (hf : Continuous f) (n : ℕ) : Continuous (f ^ n : CircleDeg1Lift) := by
  rw [coe_pow]
  exact hf.iterate n
theorem translationNumber_eq_rat_iff (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    τ f = m / n ↔ ∃ x, (f ^ n) x = x + m := by
  rw [eq_div_iff, mul_comm, ← translationNumber_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)
theorem semiconj_of_group_action_of_forall_translationNumber_eq {G : Type*} [Group G]
    (f₁ f₂ : G →* CircleDeg1Lift) (h : ∀ g, τ (f₁ g) = τ (f₂ g)) :
    ∃ F : CircleDeg1Lift, ∀ g, Semiconj F (f₁ g) (f₂ g) := by
  have : ∀ x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) := by
    refine fun x => ⟨x + 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits, MonoidHom.map_inv, translationNumber_units_inv,
        MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) ≤ f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translationNumber_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ ≤ x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 :=
        add_le_add_right (map_lt_add_translationNumber_add_one _ _).le _
      _ = x + 2 := by simp [this, add_assoc, one_add_one_eq_two]
  set F₁ := toOrderIso.comp f₁.toHomUnits
  set F₂ := toOrderIso.comp f₂.toHomUnits
  have hF₁ : ∀ g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : ∀ g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  refine ⟨⟨⟨fun x ↦ ⨆ g', (F₂ g')⁻¹ (F₁ g' x), fun x y hxy => ?_⟩, fun x => ?_⟩,
    csSup_div_semiconj F₂ F₁ fun x => ?_⟩ <;> simp only [hF₁, hF₂, ← map_inv, coe_mk]
  · exact ciSup_mono (this y) fun g => mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact (Monotone.map_ciSup_of_continuousAt (continuousAt_id.add continuousAt_const)
      (monotone_id.add_const (1 : ℝ)) (this x)).symm
  · exact this x
theorem units_semiconj_of_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂) :
    ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  have : ∀ n : Multiplicative ℤ,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) := fun n ↦ by
    simp [h]
  (semiconj_of_group_action_of_forall_translationNumber_eq _ _ this).imp fun F hF => by
    simpa using hF (Multiplicative.ofAdd 1)
theorem semiconj_of_isUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁)
    (h₂ : IsUnit f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ := by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
  exact units_semiconj_of_translationNumber_eq h
theorem semiconj_of_bijective_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : Bijective f₁)
    (h₂ : Bijective f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h
end CircleDeg1Lift