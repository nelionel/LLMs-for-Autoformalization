import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Choose.Multinomial
open Finset Nat Ideal
section DividedPowersDefinition
variable {A : Type*} [CommSemiring A] (I : Ideal A)
structure DividedPowers where
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ (n) {a : A} {x} (_ : x ∈ I),
    dpow n (a * x) = a ^ n * dpow n x
  mul_dpow : ∀ (m n) {x} (_ : x ∈ I),
    dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : ∀ (m) {n x} (_ : n ≠ 0) (_ : x ∈ I),
    dpow m (dpow n x) = uniformBell m n * dpow (m * n) x
variable (A) in
def dividedPowersBot [DecidableEq A] : DividedPowers (⊥ : Ideal A) where
  dpow n a := ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    dsimp
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero {a} ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one {a} ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a ↦ False.elim (hn a)
  dpow_add n a b ha hb := by
    rw [mem_bot.mp ha, mem_bot.mp hb, add_zero]
    simp only [true_and, ge_iff_le, tsub_eq_zero_iff_le, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      intro i hi
      simp only [mem_antidiagonal] at hi
      split_ifs with h2 h1
      · rw [h1, h2, add_zero] at hi
        exfalso
        exact h hi.symm
      · rfl
      · rfl
  dpow_mul n {a x} hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow m n {x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm: m = 0
    · simp only [hm, and_true, true_or, ite_true, uniformBell_zero_left, cast_one]
      rw [if_pos]
      exact fun h ↦ False.elim (hn h)
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]
instance [DecidableEq A] : Inhabited (DividedPowers (⊥ : Ideal A)) :=
  ⟨dividedPowersBot A⟩
instance : CoeFun (DividedPowers I) fun _ ↦ ℕ → A → A := ⟨fun hI ↦ hI.dpow⟩
variable {I} in
@[ext]
theorem DividedPowers.ext (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (_ : x ∈ I), hI.dpow n x = hI'.dpow n x) :
    hI = hI' := by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  ext n x
  by_cases hx : x ∈ I
  · exact h_eq n hx
  · rw [h₀ hx, h₀' hx]
theorem DividedPowers.coe_injective :
    Function.Injective (fun (h : DividedPowers I) ↦ (h : ℕ → A → A)) := fun hI hI' h ↦ by
  ext n x
  exact congr_fun (congr_fun h n) x
end DividedPowersDefinition
namespace DividedPowers
section BasicLemmas
variable {A : Type*} [CommSemiring A] {I : Ideal A} {a b : A}
theorem dpow_add' (hI : DividedPowers I) (n : ℕ) (ha : a ∈ I) (hb : b ∈ I) :
    hI.dpow n (a + b) = (range (n + 1)).sum fun k ↦ hI.dpow k a * hI.dpow (n - k) b := by
  rw [hI.dpow_add n ha hb, sum_antidiagonal_eq_sum_range_succ_mk]
def exp (hI : DividedPowers I) (a : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ hI.dpow n a
theorem exp_add' (dp : ℕ → A → A)
    (dp_add : ∀ n, dp n (a + b) = (antidiagonal n).sum fun k ↦ dp k.1 a * dp k.2 b) :
    PowerSeries.mk (fun n ↦ dp n (a + b)) =
      (PowerSeries.mk fun n ↦ dp n a) * (PowerSeries.mk fun n ↦ dp n b) := by
  ext n
  simp only [exp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]
theorem exp_add (hI : DividedPowers I) (ha : a ∈ I) (hb : b ∈ I) :
    hI.exp (a + b) = hI.exp a * hI.exp b :=
  exp_add' _ (fun n ↦ hI.dpow_add n ha hb)
variable (hI : DividedPowers I)
theorem dpow_smul (n : ℕ) (ha : a ∈ I) :
    hI.dpow n (b • a) = b ^ n • hI.dpow n a := by
  simp only [smul_eq_mul, hI.dpow_mul, ha]
theorem dpow_mul_right (n : ℕ) (ha : a ∈ I) :
    hI.dpow n (a * b) = hI.dpow n a * b ^ n := by
  rw [mul_comm, hI.dpow_mul n ha, mul_comm]
theorem dpow_smul_right (n : ℕ) (ha : a ∈ I) :
    hI.dpow n (a • b) = hI.dpow n a • b ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right n ha, smul_eq_mul]
theorem factorial_mul_dpow_eq_pow (n : ℕ) (ha : a ∈ I) :
    (n ! : A) * hI.dpow n a = a ^ n := by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero ha]
  | succ n ih =>
    rw [factorial_succ, mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add, cast_mul, mul_assoc,
      ← hI.mul_dpow n 1 ha, ← mul_assoc, ih, hI.dpow_one ha, pow_succ, mul_comm]
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_mul n I.zero_mem,
    zero_pow hn, zero_mul, zero_mul]
theorem nilpotent_of_mem_dpIdeal {n : ℕ} (hn : n ≠ 0) (hnI : ∀ {y} (_ : y ∈ I), n • y = 0)
    (hI : DividedPowers I) (ha : a ∈ I) : a ^ n = 0 := by
  have h_fac : (n ! : A) * hI.dpow n a =
    n • ((n - 1)! : A) * hI.dpow n a := by
    rw [nsmul_eq_mul, ← cast_mul, mul_factorial_pred (Nat.pos_of_ne_zero hn)]
  rw [← hI.factorial_mul_dpow_eq_pow n ha, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1)! : A) (hI.dpow_mem hn ha))
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [Algebra.id.smul_eq_mul, hJ.dpow_mul n hb, mul_comm a b, hI.dpow_mul n ha, ←
      hJ.factorial_mul_dpow_eq_pow n hb, ← hI.factorial_mul_dpow_eq_pow n ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add n (mul_le_right hx) (mul_le_right hy),
      hJ.dpow_add n (mul_le_left hx) (mul_le_left hy)]
    apply sum_congr rfl
    intro k _
    rw [hx', hy']
theorem prod_dpow {ι : Type*} {s : Finset ι} (n : ι → ℕ) (ha : a ∈ I) :
    (s.prod fun i ↦ hI.dpow (n i) a) = multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert hi hrec =>
    rw [prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n _) a),
      mul_assoc, mul_dpow _ _ _ ha, ← sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi, mul_comm, cast_mul, sum_insert hi]
theorem dpow_sum' {M : Type*} [AddCommMonoid M] {I : AddSubmonoid M} (dpow : ℕ → M → A)
    (dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1)
    (dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
      dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → M} (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    dpow n (s.sum x) = (s.sym n).sum fun k ↦ s.prod fun i ↦ dpow (Multiset.count i k) (x i) := by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero, sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi ↦ hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add n (hx a (mem_insert_self a s)) (I.sum_mem fun i ↦ hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ ↦ m.filterNe a)
      (fun m _ ↦ m.2.fill a m.1)
      (fun m hm ↦ mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm ↦ by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h ↦ h.2) (fun h ↦ hm b h))
      (fun m _ ↦ m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 ↦ ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← m.fill_filterNe a]
      exact Sym.count_coe_fill_of_ne (ne_of_mem_of_not_mem hi ha)
    · intro m hm
      convert sym_filterNe_mem a hm
      rw [erase_insert ha]
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    hI.dpow n (s.sum x) =
      (s.sym n).sum fun k ↦ s.prod fun i ↦ hI.dpow (Multiset.count i k) (x i) :=
  dpow_sum' hI.dpow hI.dpow_zero hI.dpow_add hI.dpow_eval_zero hx n
end BasicLemmas
section Equiv
variable {A B : Type*} [CommSemiring A] {I : Ideal A} [CommSemiring B] {J : Ideal B}
  {e : A ≃+* B} (h : I.map e = J)
def ofRingEquiv (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null {n} {x} hx := by
    rw [EmbeddingLike.map_eq_zero_iff, hI.dpow_null]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_zero {x} hx := by
    rw [EmbeddingLike.map_eq_one_iff, hI.dpow_zero]
    rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_one {x} hx := by
    simp only
    rw [dpow_one, RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem {n} {x} hn hx := by
    simp only
    rw [← h, I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add n {x y} hx hy := by
    simp only [map_add]
    rw [hI.dpow_add n (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, _root_.map_mul]
  dpow_mul n {a x} hx := by
    simp only [_root_.map_mul]
    rw [hI.dpow_mul n (symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [_root_.map_mul, map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow m n {x} hx := by
    simp only
    rw [← _root_.map_mul, hI.mul_dpow, _root_.map_mul]
    · simp only [map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
  dpow_comp m {n x} hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp _ hn]
    · simp only [_root_.map_mul, map_natCast]
    · rwa [symm_apply_mem_of_equiv_iff, h]
@[simp]
theorem ofRingEquiv_dpow (hI : DividedPowers I) (n : ℕ) (b : B) :
    (ofRingEquiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl
theorem ofRingEquiv_dpow_apply (hI : DividedPowers I) (n : ℕ) (a : A) :
    (ofRingEquiv h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp
def equiv : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv h
  invFun := ofRingEquiv (show map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI ↦ by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ ↦ by ext n b; simp [ofRingEquiv]
theorem equiv_apply (hI : DividedPowers I) (n : ℕ) (b : B) :
    (equiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl
theorem equiv_apply' (hI : DividedPowers I) (n : ℕ) (a : A) :
    (equiv h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_dpow_apply h hI n a
end Equiv
end DividedPowers