import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Prime.Int
universe u
open Nat
open Rat
open multiplicity
namespace padicValNat
open multiplicity
variable {p : ℕ}
@[simp]
theorem self (hp : 1 < p) : padicValNat p p = 1 := by
  simp [padicValNat_def', zero_lt_one.trans hp, hp.ne']
theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h
open Nat.maxPowDiv
theorem maxPowDiv_eq_emultiplicity {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv n = emultiplicity p n := by
  apply (emultiplicity_eq_of_dvd_of_not_dvd (pow_dvd p n) _).symm
  intro h
  apply Nat.not_lt.mpr <| le_of_dvd hp hn h
  simp
theorem maxPowDiv_eq_multiplicity {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (h : Finite p n) :
    p.maxPowDiv n = multiplicity p n := by
  exact_mod_cast h.emultiplicity_eq_multiplicity ▸ maxPowDiv_eq_emultiplicity hp hn
@[csimp]
theorem padicValNat_eq_maxPowDiv : @padicValNat = @maxPowDiv := by
  ext p n
  by_cases h : 1 < p ∧ 0 < n
  · rw [padicValNat_def' h.1.ne' h.2, maxPowDiv_eq_multiplicity h.1 h.2]
    exact Nat.multiplicity_finite_iff.2 ⟨h.1.ne', h.2⟩
  · simp only [not_and_or,not_gt_eq,Nat.le_zero] at h
    apply h.elim
    · intro h
      interval_cases p
      · simp [Classical.em]
      · dsimp [padicValNat, maxPowDiv]
        rw [go, if_neg]; simp
    · intro h
      simp [h]
end padicValNat
def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs
namespace padicValInt
open multiplicity
variable {p : ℕ}
theorem of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValInt p z = multiplicity (p : ℤ) z:= by
  rw [padicValInt, padicValNat_def' hp (Int.natAbs_pos.mpr hz)]
  apply Int.multiplicity_natAbs
@[simp]
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]
@[simp]
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]
@[simp]
theorem of_nat {n : ℕ} : padicValInt p n = padicValNat p n := by simp [padicValInt]
theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]
theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  rw [padicValInt, padicValNat.eq_zero_iff]
  right; right
  rwa [← Int.ofNat_dvd_left]
end padicValInt
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
lemma padicValRat_def (p : ℕ) (q : ℚ) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl
namespace padicValRat
open multiplicity
variable {p : ℕ}
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]
@[simp]
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]
@[simp]
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]
@[simp]
theorem of_int {z : ℤ} : padicValRat p z = padicValInt p z := by simp [padicValRat]
theorem of_int_multiplicity {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = multiplicity (p : ℤ) z := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]
theorem multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q = multiplicity (p : ℤ) q.num - multiplicity p q.den := by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq),
    padicValNat_def' hp q.pos]
@[simp]
theorem of_nat {n : ℕ} : padicValRat p n = padicValNat p n := by simp [padicValRat]
theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]
end padicValRat
section padicValNat
variable {p : ℕ}
theorem zero_le_padicValRat_of_nat (n : ℕ) : 0 ≤ padicValRat p n := by simp
@[norm_cast]
theorem padicValRat_of_nat (n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by simp
@[simp]
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).pos]
  simp
theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← WithTop.coe_le_coe, ENat.some_eq_coe, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]
theorem dvd_iff_padicValNat_ne_zero {p n : ℕ} [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0.bot_lt h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩
end padicValNat
namespace padicValRat
open multiplicity
variable {p : ℕ} [hp : Fact p.Prime]
theorem finite_int_prime_iff {a : ℤ} : Finite (p : ℤ) a ↔ a ≠ 0 := by
  simp [Int.multiplicity_finite_iff, hp.1.ne_one]
protected theorem defn (p : ℕ) [hp : Fact p.Prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
    (qdf : q = n /. d) :
    padicValRat p q = multiplicity (p : ℤ) n - multiplicity (p : ℤ) d := by
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [Nat.isUnit_iff, hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1),
    multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]
  · rw [Nat.cast_add, Nat.cast_add]
    simp_rw [Int.natCast_multiplicity p q.den]
    ring
  · simpa [finite_int_prime_iff, hc2] using hd
  · simpa [finite_int_prime_iff, hqz, hc2] using hd
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, Nat.cast_mul]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← q.num_divInt_den, padicValRat.defn p hq', ← r.num_divInt_den, padicValRat.defn p hr']
  rw [multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add]
  · ring
  · simp [finite_int_prime_iff]
  · simp [finite_int_prime_iff, hq, hr]
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]
protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv r, sub_eq_add_neg]
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔
      ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ := by
  have hf1 : Finite (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : Finite (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ←
      add_sub_assoc, _root_.le_sub_iff_add_le]
    norm_cast
    rw [← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf1, add_comm,
        ← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf2,
        hf1.multiplicity_le_multiplicity_iff hf2]
theorem le_padicValRat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0)
    (h : padicValRat p q ≤ padicValRat p r) : padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
      have hqrd : q.num * r.den + q.den * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← q.num_divInt_den]
      rw [hqreq, padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        emultiplicity_le_emultiplicity_iff, mul_left_comm,
        emultiplicity_mul (Nat.prime_iff_prime_int.1 hp.1), add_mul]
      rw [← q.num_divInt_den, ← r.num_divInt_den, padicValRat_le_padicValRat_iff hqn hrn hqd hrd, ←
        emultiplicity_le_emultiplicity_iff] at h
      calc
        _ ≤
            min (emultiplicity (↑p) (q.num * r.den * q.den))
              (emultiplicity (↑p) (↑q.den * r.num * ↑q.den)) :=
          le_min
            (by rw [emultiplicity_mul (a :=_ * _) (Nat.prime_iff_prime_int.1 hp.1), add_comm])
            (by
              rw [mul_assoc,
                  emultiplicity_mul (b := _ * _) (Nat.prime_iff_prime_int.1 hp.1)]
              exact add_le_add_left h _)
        _ ≤ _ := min_le_emultiplicity_add
theorem min_le_padicValRat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)
lemma add_eq_min {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hval : padicValRat p q ≠ padicValRat p r) :
    padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right, padicValRat.neg] at h2 h3
  rw [add_comm] at h3
  refine le_antisymm (le_min ?_ ?_) h1
  · contrapose! h2
    rw [min_eq_right h2.le] at h3
    exact lt_min h2 (lt_of_le_of_ne h3 hval)
  · contrapose! h3
    rw [min_eq_right h3.le] at h2
    exact lt_min h3 (lt_of_le_of_ne h2 hval.symm)
lemma add_eq_of_lt {q r : ℚ} (hqr : q + r ≠ 0)
    (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q < padicValRat p r) :
    padicValRat p (q + r) = padicValRat p q := by
  rw [add_eq_min hqr hq hr (ne_of_lt hval), min_eq_left (le_of_lt hval)]
lemma lt_add_of_lt {q r₁ r₂ : ℚ} (hqr : r₁ + r₂ ≠ 0)
    (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
    padicValRat p q < padicValRat p (r₁ + r₂) :=
  lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)
@[simp]
lemma self_pow_inv (r : ℕ) : padicValRat p ((p : ℚ) ^ r)⁻¹ = -r := by
  rw [padicValRat.inv, neg_inj, padicValRat.pow (Nat.cast_ne_zero.mpr hp.elim.ne_zero),
      padicValRat.self hp.elim.one_lt, mul_one]
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : ∑ i ∈ Finset.range n, F i ≠ 0) : 0 < padicValRat p (∑ i ∈ Finset.range n, F i) := by
  induction' n with d hd
  · exact False.elim (hn0 rfl)
  · rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x ∈ Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min (hd (fun i hi => ?_) h) (hF d (lt_add_one _))
      exact hF _ (lt_trans hi (lt_add_one _))
theorem lt_sum_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)] {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hF : ∀ i, i ∈ S → padicValRat p (F j) < padicValRat p (F i))
    (hn1 : ∀ i : ℕ, 0 < F i) : padicValRat p (F j) < padicValRat p (∑ i ∈ S, F i) := by
  induction' hS using Finset.Nonempty.cons_induction with k s S' Hnot Hne Hind
  · rw [Finset.sum_singleton]
    exact hF k (by simp)
  · rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert,Finset.mem_insert]; exact Or.inr hi)))
end padicValRat
namespace padicValNat
variable {p a b : ℕ} [hp : Fact p.Prime]
protected theorem mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
  mod_cast padicValRat.mul (p := p) (q := a) (r := b)
protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul hk hb, Nat.add_sub_cancel]
protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd, padicValNat_self]
protected theorem pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simpa only [← @Nat.cast_inj ℤ, push_cast] using padicValRat.pow (Nat.cast_ne_zero.mpr ha)
@[simp]
protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow _ (@Fact.out p.Prime).ne_zero, padicValNat_self, mul_one]
protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd, padicValNat.prime_pow]
protected theorem div' {m : ℕ} (cpm : Coprime p m) {b : ℕ} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]
end padicValNat
section padicValNat
variable {p : ℕ}
theorem dvd_of_one_le_padicValNat {n : ℕ} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)
theorem pow_padicValNat_dvd {n : ℕ} : p ^ padicValNat p n ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn); · simp
  rcases eq_or_ne p 1 with (rfl | hp); · simp
  apply pow_dvd_of_le_multiplicity
  rw [padicValNat_def'] <;> assumption
theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity (Nat.pos_of_ne_zero ha),
    Nat.cast_le]
theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le ha, or_iff_right ha]
theorem pow_succ_padicValNat_not_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn, not_le]
  exact Nat.lt_succ_self _
theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (neq : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp neq
theorem padicValNat_prime_prime_pow {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : ℕ) (neq : p ≠ q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _ <| Nat.Prime.ne_zero hq.elim, padicValNat_primes neq, mul_zero]
theorem padicValNat_mul_pow_left {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (neq : p ≠ q) : padicValNat p (p^n * q^m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p^n)).symm (NeZero.ne' (q^m)).symm,
    padicValNat.prime_pow, padicValNat_prime_prime_pow m neq, add_zero]
theorem padicValNat_mul_pow_right {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (neq : q ≠ p) : padicValNat q (p^n * q^m) = m := by
  rw [mul_comm (p^n) (q^m)]
  exact padicValNat_mul_pow_left m n neq
lemma padicValNat_le_nat_log (n : ℕ) : padicValNat p n ≤ Nat.log p n := by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)
lemma nat_log_eq_padicValNat_iff {n : ℕ} [hp : Fact (Nat.Prime p)] (hn : 0 < n) :
    Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out, by omega⟩), and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd hn pow_padicValNat_dvd
lemma Nat.log_ne_padicValNat_succ {n : ℕ} (hn : n ≠ 0) : log 2 n ≠ padicValNat 2 (n + 1) := by
  rw [Ne, log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff, ← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff, Nat.pow_succ] at h2
  refine not_dvd_of_between_consec_multiples h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  exact pow_succ_padicValNat_not_dvd (p := 2) n.succ_ne_zero ∘ dvd_of_eq
lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : ℕ) :
    max (log 2 n) (padicValNat 2 (n + 1)) = log 2 (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le one_lt_two (pow_log_le_add_one 2 n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt one_lt_two h))
    (pow_log_le_self 2 n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]
theorem range_pow_padicValNat_subset_divisors {n : ℕ} (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) ⊆ n.divisors := by
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by omega).trans pow_padicValNat_dvd, hn⟩
theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'
theorem padicValNat_factorial_mul (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n) ! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity <| factorial_pos (p * n), Nat.cast_add,
      padicValNat_eq_emultiplicity <| factorial_pos n]
  exact Prime.emultiplicity_factorial_mul hp.out
theorem padicValNat_eq_zero_of_mem_Ioo {m k : ℕ}
    (hm : m ∈ Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0 :=
  padicValNat.eq_zero_of_not_dvd <| not_dvd_of_between_consec_multiples hm.1 hm.2
theorem padicValNat_factorial_mul_add {n : ℕ} (m : ℕ) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n) ! = padicValNat p (p * m) ! := by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ, factorial_succ,
      padicValNat.mul (succ_ne_zero (p * m + n)) <| factorial_ne_zero (p * m + _),
      hn <| lt_of_succ_lt h, ← add_succ,
      padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n),
        (Nat.mul_add _ _ _▸ Nat.mul_one _ ▸ ((add_lt_add_iff_left (p * m)).mpr h))⟩,
      zero_add]
@[simp] theorem padicValNat_mul_div_factorial (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm
theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_pos _) ▸
      Prime.emultiplicity_factorial hp.out hnb)
theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt.base (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one, ← Finset.sum_Ico_add' _ 0 _ 1,
    Ico_zero_eq_range, ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, Nat.succ_eq_add_one]
theorem padicValNat_choose {n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : log p n < b) :
    padicValNat p (choose n k) =
    ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_pos hkn) ▸
    Prime.emultiplicity_choose hp.out hkn hnb
theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
    padicValNat p (choose (n + k) k) =
    ((Finset.Ico 1 b).filter fun i => p ^ i ≤ k % p ^ i + n % p ^ i).card := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_pos <|
    Nat.le_add_left k n)▸ Prime.emultiplicity_choose' hp.out hnb
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k ≤ n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h, Nat.mul_sub_left_distrib,
      padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _), Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k, Nat.add_sub_cancel n k, ← Nat.add_sub_assoc <|
      digit_sum_le p n, Nat.sub_sub (k + n), ← Nat.sub_right_comm, Nat.sub_sub, sub_add_eq,
      add_comm, tsub_tsub_assoc (Nat.le_refl (k + n)) <| (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k)), Nat.sub_self (k + n), zero_add, add_comm]
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : ℕ} [hp : Fact p.Prime]
    (h : k ≤ n) : (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  convert @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals omega
end padicValNat
section padicValInt
variable {p : ℕ} [hp : Fact p.Prime]
theorem padicValInt_dvd_iff (n : ℕ) (a : ℤ) : (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.natAbs_eq_zero, ← padicValNat_dvd_iff, ← Int.natCast_dvd, Int.natCast_pow]
theorem padicValInt_dvd (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  rw [padicValInt_dvd_iff]
  exact Or.inr le_rfl
theorem padicValInt_self : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt
theorem padicValInt.mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul, padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]
theorem padicValInt_mul_eq_succ (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [eq_self_iff_true, padicValInt.of_nat, padicValNat_self]
end padicValInt