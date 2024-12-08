import Mathlib.RingTheory.Fintype
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1
theorem strictMono_mersenne : StrictMono mersenne := fun m n h ↦
  (Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 <| by gcongr; norm_num1
@[simp]
theorem mersenne_lt_mersenne {p q : ℕ} : mersenne p < mersenne q ↔ p < q :=
  strictMono_mersenne.lt_iff_lt
@[gcongr] protected alias ⟨_, GCongr.mersenne_lt_mersenne⟩ := mersenne_lt_mersenne
@[simp]
theorem mersenne_le_mersenne {p q : ℕ} : mersenne p ≤ mersenne q ↔ p ≤ q :=
  strictMono_mersenne.le_iff_le
@[gcongr] protected alias ⟨_, GCongr.mersenne_le_mersenne⟩ := mersenne_le_mersenne
@[simp] theorem mersenne_zero : mersenne 0 = 0 := rfl
@[simp] lemma mersenne_odd : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0
  | 0 => by simp
  | p + 1 => by
    simpa using Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero p.succ_ne_zero) odd_one
@[simp] theorem mersenne_pos {p : ℕ} : 0 < mersenne p ↔ 0 < p := mersenne_lt_mersenne (p := 0)
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function
alias ⟨_, mersenne_pos_of_pos⟩ := mersenne_pos
@[positivity mersenne _]
def evalMersenne : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(mersenne $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(mersenne_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Nat.zero_le (mersenne $a)))
  | _, _, _ => throwError "not mersenne"
end Mathlib.Meta.Positivity
@[simp]
theorem one_lt_mersenne {p : ℕ} : 1 < mersenne p ↔ 1 < p :=
  mersenne_lt_mersenne (p := 1)
@[simp]
theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne, tsub_add_cancel_of_le]
  exact one_le_pow₀ (by norm_num)
namespace LucasLehmer
open Nat
def s : ℕ → ℤ
  | 0 => 4
  | i + 1 => s i ^ 2 - 2
def sZMod (p : ℕ) : ℕ → ZMod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => sZMod p i ^ 2 - 2
def sMod (p : ℕ) : ℕ → ℤ
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (sMod p i ^ 2 - 2) % (2 ^ p - 1)
theorem mersenne_int_pos {p : ℕ} (hp : p ≠ 0) : (0 : ℤ) < 2 ^ p - 1 :=
  sub_pos.2 <| mod_cast Nat.one_lt_two_pow hp
theorem mersenne_int_ne_zero (p : ℕ) (hp : p ≠ 0) : (2 ^ p - 1 : ℤ) ≠ 0 :=
  (mersenne_int_pos hp).ne'
theorem sMod_nonneg (p : ℕ) (hp : p ≠ 0) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp
theorem sMod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]
theorem sMod_lt (p : ℕ) (hp : p ≠ 0) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  refine (Int.emod_lt _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le
theorem sZMod_eq_s (p' : ℕ) (i : ℕ) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction' i with i ih
  · dsimp [s, sZMod]
    norm_num
  · push_cast [s, sZMod, ih]; rfl
theorem Int.natCast_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1 := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  norm_cast
@[deprecated (since := "2024-05-25")] alias Int.coe_nat_pow_pred := Int.natCast_pow_pred
theorem Int.coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  Int.natCast_pow_pred 2 p (by decide)
theorem sZMod_eq_sMod (p : ℕ) (i : ℕ) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl
def lucasLehmerResidue (p : ℕ) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)
theorem residue_eq_zero_iff_sMod_eq_zero (p : ℕ) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · 
    intro h
    simp? [ZMod.intCast_zmod_eq_zero_iff_dvd] at h says
      simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, ofNat_pos, pow_pos, cast_pred,
        cast_pow, cast_ofNat] at h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _ h <;> clear h
    · exact sMod_nonneg _ (by positivity) _
    · exact sMod_lt _ (by positivity) _
  · intro h
    rw [h]
    simp
def LucasLehmerTest (p : ℕ) : Prop :=
  lucasLehmerResidue p = 0
def q (p : ℕ) : ℕ+ :=
  ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩
def X (q : ℕ+) : Type :=
  ZMod q × ZMod q
namespace X
variable {q : ℕ+}
instance : Inhabited (X q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
instance : Fintype (X q) := inferInstanceAs (Fintype (ZMod q × ZMod q))
instance : DecidableEq (X q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))
@[ext]
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; congr
@[simp] theorem zero_fst : (0 : X q).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : X q).2 = 0 := rfl
@[simp]
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl
@[simp]
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl
@[simp]
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl
@[simp]
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl
instance : Mul (X q) where mul x y := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)
@[simp]
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl
@[simp]
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl
instance : One (X q) where one := ⟨1, 0⟩
@[simp]
theorem one_fst : (1 : X q).1 = 1 :=
  rfl
@[simp]
theorem one_snd : (1 : X q).2 = 0 :=
  rfl
instance : Monoid (X q) :=
  { inferInstanceAs (Mul (X q)), inferInstanceAs (One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }
instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩
@[simp] theorem fst_natCast (n : ℕ) : (n : X q).fst = (n : ZMod q) := rfl
@[simp] theorem snd_natCast (n : ℕ) : (n : X q).snd = (0 : ZMod q) := rfl
@[simp] theorem ofNat_fst (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).fst = OfNat.ofNat n :=
  rfl
@[simp] theorem ofNat_snd (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).snd = 0 :=
  rfl
instance : AddGroupWithOne (X q) :=
  { inferInstanceAs (Monoid (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ ↦ by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun n => by ext <;> simp }
theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp <;> ring
theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring
instance : Ring (X q) :=
  { inferInstanceAs (AddGroupWithOne (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ ↦ by ext <;> simp
    zero_mul := fun _ ↦ by ext <;> simp }
instance : CommRing (X q) :=
  { inferInstanceAs (Ring (X q)) with
    mul_comm := fun _ _ ↦ by ext <;> dsimp <;> ring }
instance [Fact (1 < (q : ℕ))] : Nontrivial (X q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩
@[simp]
theorem fst_intCast (n : ℤ) : (n : X q).fst = (n : ZMod q) :=
  rfl
@[simp]
theorem snd_intCast (n : ℤ) : (n : X q).snd = (0 : ZMod q) :=
  rfl
@[deprecated (since := "2024-05-25")] alias nat_coe_fst := fst_natCast
@[deprecated (since := "2024-05-25")] alias nat_coe_snd := snd_natCast
@[deprecated (since := "2024-05-25")] alias int_coe_fst := fst_intCast
@[deprecated (since := "2024-05-25")] alias int_coe_snd := snd_intCast
@[norm_cast]
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by ext <;> simp
@[norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by ext <;> simp
@[deprecated (since := "2024-04-05")] alias coe_nat := coe_natCast
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  dsimp [X]
  rw [Fintype.card_prod, ZMod.card q, sq]
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  convert card_units_lt (X q)
  rw [card_eq]
def ω : X q := (2, 1)
def ωb : X q := (2, -1)
theorem ω_mul_ωb (q : ℕ+) : (ω : X q) * ωb = 1 := by
  dsimp [ω, ωb]
  ext <;> simp; ring
theorem ωb_mul_ω (q : ℕ+) : (ωb : X q) * ω = 1 := by
  rw [mul_comm, ω_mul_ωb]
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction' i with i ih
  · dsimp [s, ω, ωb]
    ext <;> norm_num
  · calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel_right]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ]
end X
open X
theorem two_lt_q (p' : ℕ) : 2 < q (p' + 2) := by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow
theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  simp? [ZMod.intCast_zmod_eq_zero_iff_dvd] at h says
    simp only [add_tsub_cancel_right, ZMod.intCast_zmod_eq_zero_iff_dvd, ofNat_pos,
      pow_pos, cast_pred, cast_pow, cast_ofNat] at h
  cases' h with k h
  use k
  replace h := congr_arg (fun n : ℤ => (n : X (q (p' + 2)))) h
  dsimp at h
  rw [closed_form] at h
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  dsimp at h
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add, ← pow_add ω, t, ← mul_pow ω ωb (2 ^ p'), ω_mul_ωb, one_pow] at h
  rw [mul_comm, coe_mul] at h
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  replace h := eq_sub_of_add_eq h
  have : 1 ≤ 2 ^ (p' + 2) := Nat.one_le_pow _ _ (by decide)
  exact mod_cast h
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.natCast_zmod_eq_zero_iff_dvd, -pow_pos]
  apply Nat.minFac_dvd
theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  cases' ω_pow_formula p' h with k w
  rw [mersenne_coe_X] at w
  simpa using w
theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp
def ωUnit (p : ℕ) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := ω_mul_ωb _
  inv_val := ωb_mul_ω _
@[simp]
theorem ωUnit_coe (p : ℕ) : (ωUnit p : X (q p)) = ω :=
  rfl
theorem order_ω (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  · exact Nat.prime_two
  · intro o
    have ω_pow := orderOf_dvd_iff_pow_eq_one.1 o
    replace ω_pow :=
      congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) ω_pow
    simp? at ω_pow says
      simp only [Units.coeHom_apply, Units.val_pow_eq_pow_val, ωUnit_coe, Units.val_one] at ω_pow
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    haveI : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    apply ZMod.neg_one_ne_one h.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h
theorem order_ineq (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ ≤ Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < (q (p' + 2) : ℕ) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))
end LucasLehmer
export LucasLehmer (LucasLehmerTest lucasLehmerResidue)
open LucasLehmer
theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime := by
  let p' := p - 2
  have z : p = p' + 2 := (tsub_eq_iff_eq_add_of_le w.nat_succ_le).mp rfl
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  rw [z] at a
  rw [z] at t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  exact not_lt_of_ge (Nat.sub_le _ _) h
namespace LucasLehmer
namespace norm_num_ext
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum
def sModNat (q : ℕ) : ℕ → ℕ
  | 0 => 4 % q
  | i + 1 => (sModNat q i ^ 2 + (q - 2)) % q
theorem sModNat_eq_sMod (p k : ℕ) (hp : 2 ≤ p) : (sModNat (2 ^ p - 1) k : ℤ) = sMod p k := by
  have h1 := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_of_le_right (by norm_num) hp
  have h2 : 1 ≤ 2 ^ p := by omega
  induction k with
  | zero =>
    rw [sModNat, sMod, Int.ofNat_emod]
    simp [h2]
  | succ k ih =>
    rw [sModNat, sMod, ← ih]
    have h3 : 2 ≤ 2 ^ p - 1 := by
      zify [h2]
      calc
        (2 : Int) ≤ 4 - 1 := by norm_num
        _         ≤ 2 ^ p - 1 := by zify at h1; exact Int.sub_le_sub_right h1 _
    zify [h2, h3]
    rw [← add_sub_assoc, sub_eq_add_neg, add_assoc, add_comm _ (-2), ← add_assoc,
      Int.add_emod_self, ← sub_eq_add_neg]
def sModNatTR (q : ℕ) (k : Nat) : ℕ :=
  go k (4 % q)
where
  go : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => go n ((acc ^ 2 + (q - 2)) % q)
def sModNat_aux (b : ℕ) (q : ℕ) : ℕ → ℕ
  | 0 => b
  | i + 1 => (sModNat_aux b q i ^ 2 + (q - 2)) % q
theorem sModNat_aux_eq (q k : ℕ) : sModNat_aux (4 % q) q k = sModNat q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNat_aux, ih, sModNat, ← ih]
theorem sModNatTR_eq_sModNat (q : ℕ) (i : ℕ) : sModNatTR q i = sModNat q i := by
  rw [sModNatTR, helper, sModNat_aux_eq]
where
  helper b q k : sModNatTR.go q k b = sModNat_aux b q k := by
    induction k generalizing b with
    | zero => rfl
    | succ k ih =>
      rw [sModNatTR.go, ih, sModNat_aux]
      clear ih
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [sModNat_aux, ih, sModNat_aux]
lemma testTrueHelper (p : ℕ) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p - 1) (p - 2) = 0) :
    LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat, h]
  rfl
lemma testFalseHelper (p : ℕ) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sModNatTR (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq, Nat.succ_le, Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat]
  simpa using h
theorem isNat_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → LucasLehmerTest np → LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h
theorem isNat_not_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → ¬ LucasLehmerTest np → ¬ LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h
@[norm_num LucasLehmer.LucasLehmerTest (_ : ℕ)]
def evalLucasLehmerTest : NormNumExt where eval {_ _} e := do
  let .app _ (p : Q(ℕ)) ← Meta.whnfR e | failure
  let ⟨ep, hp⟩ ← deriveNat p _
  let np := ep.natLit!
  unless 1 < np do
    failure
  haveI' h1ltp : Nat.blt 1 $ep =Q true := ⟨⟩
  if sModNatTR (2 ^ np - 1) (np - 2) = 0 then
    haveI' hs : sModNatTR (2 ^ $ep - 1) ($ep - 2) =Q 0 := ⟨⟩
    have pf : Q(LucasLehmerTest $ep) := q(testTrueHelper $ep $h1ltp $hs)
    have pf' : Q(LucasLehmerTest $p) := q(isNat_lucasLehmerTest $hp $pf)
    return .isTrue pf'
  else
    haveI' hs : Nat.ble 1 (sModNatTR (2 ^ $ep - 1) ($ep - 2)) =Q true := ⟨⟩
    have pf : Q(¬ LucasLehmerTest $ep) := q(testFalseHelper $ep $h1ltp $hs)
    have pf' : Q(¬ LucasLehmerTest $p) := q(isNat_not_lucasLehmerTest $hp $pf)
    return .isFalse pf'
end norm_num_ext
end LucasLehmer
theorem modEq_mersenne (n k : ℕ) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1] :=
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_lt <| pow_pos zero_lt_two _).mul_right _).add_right _
    _ = k / 2 ^ n + k % 2 ^ n := by rw [one_mul]