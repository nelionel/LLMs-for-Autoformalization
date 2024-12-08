import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Nat.Multiplicity
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.IsPoly
namespace WittVector
variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]
local notation "𝕎" => WittVector p 
noncomputable section
open MvPolynomial Finset
variable (p)
def frobeniusPolyRat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n + 1) (xInTermsOfW p ℚ n)
theorem bind₁_frobeniusPolyRat_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n + 1) := by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁, bind₁_xInTermsOfW_wittPolynomial, bind₁_X_right, Function.comp_apply]
local notation "v" => multiplicity
noncomputable def frobeniusPolyAux : ℕ → MvPolynomial ℕ ℤ
  | n => X (n + 1) -  ∑ i : Fin n, have _ := i.is_lt
      ∑ j ∈ range (p ^ (n - i)),
        (((X (i : ℕ) ^ p) ^ (p ^ (n - (i : ℕ)) - (j + 1)) : MvPolynomial ℕ ℤ) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : ℕ) : ℤ)
omit hp in
theorem frobeniusPolyAux_eq (n : ℕ) :
    frobeniusPolyAux p n =
      X (n + 1) - ∑ i ∈ range n,
          ∑ j ∈ range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobeniusPolyAux p i ^ (j + 1) *
              C ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p (j + 1)) *
                ↑p ^ (j - v p (j + 1)) : ℕ) := by
  rw [frobeniusPolyAux, ← Fin.sum_univ_eq_sum_range]
def frobeniusPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  X n ^ p + C (p : ℤ) * frobeniusPolyAux p n
theorem map_frobeniusPoly.key₁ (n j : ℕ) (hj : j < p ^ n) :
    p ^ (n - v p (j + 1)) ∣ (p ^ n).choose (j + 1) := by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]
theorem map_frobeniusPoly.key₂ {n i j : ℕ} (hi : i ≤ n) (hj : j < p ^ (n - i)) :
    j - v p (j + 1) + n = i + j + (n - i - v p (j + 1)) := by
  generalize h : v p (j + 1) = m
  rsuffices ⟨h₁, h₂⟩ : m ≤ n - i ∧ m ≤ j
  · rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m ≤ j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (pow_multiplicity_dvd _ _)
  exact ⟨(Nat.pow_le_pow_iff_right hp.1.one_lt).1 (hle.trans hj),
     Nat.le_of_lt_succ ((m.lt_pow_self hp.1.one_lt).trans_le hle)⟩
theorem map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n := by
  rw [frobeniusPoly, RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_C, map_X, eq_intCast,
    Int.cast_natCast, frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : ℚ) ^ n * ⅟ (p : ℚ) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right, Function.comp_apply, wittPolynomial_eq_sum_C_mul_X_pow, sum_range_succ,
    sum_range_succ, tsub_self, add_tsub_cancel_left, pow_zero, pow_one, pow_one, sub_mul, add_mul,
    add_mul, mul_right_comm, mul_right_comm (C ((p : ℚ) ^ (n + 1))), ← C_mul, ← C_mul, pow_succ',
    mul_assoc (p : ℚ) ((p : ℚ) ^ n), h1, mul_one, C_1, one_mul, add_comm _ (X n ^ p), add_assoc,
    ← add_sub, add_right_inj, frobeniusPolyAux_eq, RingHom.map_sub, map_X, mul_sub, sub_eq_add_neg,
    add_comm _ (C (p : ℚ) * X (n + 1)), ← add_sub,
    add_right_inj, neg_eq_iff_eq_neg, neg_sub, eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p), add_pow, sum_range_succ', pow_zero, tsub_zero, Nat.choose_zero_right,
    one_mul, Nat.cast_one, mul_one, mul_add, add_mul, Nat.succ_sub (le_of_lt hi),
    Nat.succ_eq_add_one (n - i), pow_succ', pow_mul, add_sub_cancel_right, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow,
    RingHom.map_pow, RingHom.map_pow, map_C, map_X, mul_pow]
  rw [mul_comm (C (p : ℚ) ^ i), mul_comm _ ((X i ^ p) ^ _), mul_comm (C (p : ℚ) ^ (j + 1)),
    mul_comm (C (p : ℚ))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← RingHom.map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  simp only [Nat.cast_pow, pow_add, pow_one]
  suffices
    (((p ^ (n - i)).choose (j + 1) : ℚ) * (p : ℚ) ^ (j - v p (j + 1)) * p * (p ^ n : ℚ))
      = (p : ℚ) ^ j * p * ↑((p ^ (n - i)).choose (j + 1) * p ^ i) *
        (p : ℚ) ^ (n - i - v p (j + 1)) by
    have aux : ∀ k : ℕ, (p : ℚ)^ k ≠ 0 := by
      intro; apply pow_ne_zero; exact mod_cast hp.1.ne_zero
    simpa [aux, -one_div, -pow_eq_zero_iff', field_simps] using this.symm
  rw [mul_comm _ (p : ℚ), mul_assoc, mul_assoc, ← pow_add,
    map_frobeniusPoly.key₂ p hi.le hj, Nat.cast_mul, Nat.cast_pow]
  ring
theorem frobeniusPoly_zmod (n : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p := by
  rw [frobeniusPoly, RingHom.map_add, RingHom.map_pow, RingHom.map_mul, map_X, map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]
@[simp]
theorem bind₁_frobeniusPoly_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPoly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n + 1) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_frobeniusPoly, bind₁_frobeniusPolyRat_wittPolynomial,
    map_wittPolynomial]
variable {p}
def frobeniusFun (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)
omit hp in
theorem coeff_frobeniusFun (x : 𝕎 R) (n : ℕ) :
    coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) := by
  rw [frobeniusFun, coeff_mk]
variable (p)
instance frobeniusFun_isPoly : IsPoly p fun R _ Rcr => @frobeniusFun p R _ Rcr :=
  ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobeniusFun⟩⟩
variable {p}
@[ghost_simps]
theorem ghostComponent_frobeniusFun (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobeniusFun x) = ghostComponent (n + 1) x := by
  simp only [ghostComponent_apply, frobeniusFun, coeff_mk, ← bind₁_frobeniusPoly_wittPolynomial,
    aeval_bind₁]
def frobenius : 𝕎 R →+* 𝕎 R where
  toFun := frobeniusFun
  map_zero' := by
    refine IsPoly.ext (@IsPoly.comp p _ _ (frobeniusFun_isPoly p) WittVector.zeroIsPoly)
      (@IsPoly.comp p _ _ WittVector.zeroIsPoly
      (frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_zero, forall_const]
    ghost_simp
  map_one' := by
    refine
      IsPoly.ext (@IsPoly.comp p _ _ (frobeniusFun_isPoly p) WittVector.oneIsPoly)
        (@IsPoly.comp p _ _ WittVector.oneIsPoly (frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_one, forall_const]
    ghost_simp
  map_add' := by dsimp only; ghost_calc _ _; ghost_simp
  map_mul' := by dsimp only; ghost_calc _ _; ghost_simp
theorem coeff_frobenius (x : 𝕎 R) (n : ℕ) :
    coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) :=
  coeff_frobeniusFun _ _
@[ghost_simps]
theorem ghostComponent_frobenius (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobenius x) = ghostComponent (n + 1) x :=
  ghostComponent_frobeniusFun _ _
variable (p)
instance frobenius_isPoly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobeniusFun_isPoly _
section CharP
variable [CharP R p]
@[simp]
theorem coeff_frobenius_charP (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = x.coeff n ^ p := by
  rw [coeff_frobenius]
  letI : Algebra (ZMod p) R := ZMod.algebra _ _
  calc
    aeval (fun k => x.coeff k) (frobeniusPoly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n)) := ?_
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial ℕ (ZMod p)) := ?_
    _ = x.coeff n ^ p := ?_
  · conv_rhs => rw [aeval_eq_eval₂Hom, eval₂Hom_map_hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobeniusPoly_zmod]
  · rw [map_pow, aeval_X]
theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R p) := by
  ext (x n)
  simp only [coeff_frobenius_charP, map_coeff, frobenius_def]
@[simp]
theorem frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius x = x := by
  simp only [WittVector.ext_iff, coeff_frobenius_charP, ZMod.pow_card, eq_self_iff_true,
    forall_const]
variable (R)
@[simps (config := .asFn)]
def frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R :=
  { (WittVector.frobenius : WittVector p R →+* WittVector p R) with
    toFun := WittVector.frobenius
    invFun := map (_root_.frobeniusEquiv R p).symm
    left_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobeniusEquiv_symm_apply_frobenius R p _
    right_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobenius_apply_frobeniusEquiv_symm R p _ }
theorem frobenius_bijective [PerfectRing R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) :=
  (frobeniusEquiv p R).bijective
end CharP
end
end WittVector