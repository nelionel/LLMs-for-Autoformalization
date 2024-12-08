import Mathlib.NumberTheory.Transcendental.Liouville.Basic
noncomputable section
open scoped Nat
open Real Finset
def liouvilleNumber (m : ℝ) : ℝ :=
  ∑' i : ℕ, 1 / m ^ i !
namespace LiouvilleNumber
def partialSum (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), 1 / m ^ i !
def remainder (m : ℝ) (k : ℕ) : ℝ :=
  ∑' i, 1 / m ^ (i + (k + 1))!
protected theorem summable {m : ℝ} (hm : 1 < m) : Summable fun i : ℕ => 1 / m ^ i ! :=
  summable_one_div_pow_of_le hm Nat.self_le_factorial
theorem remainder_summable {m : ℝ} (hm : 1 < m) (k : ℕ) :
    Summable fun i : ℕ => 1 / m ^ (i + (k + 1))! := by
  convert (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)
theorem remainder_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < remainder m k :=
  tsum_pos (remainder_summable hm k) (fun _ => by positivity) 0 (by positivity)
theorem partialSum_succ (m : ℝ) (n : ℕ) :
    partialSum m (n + 1) = partialSum m n + 1 / m ^ (n + 1)! :=
  sum_range_succ _ _
theorem partialSum_add_remainder {m : ℝ} (hm : 1 < m) (k : ℕ) :
    partialSum m k + remainder m k = liouvilleNumber m :=
  sum_add_tsum_nat_add _ (LiouvilleNumber.summable hm)
theorem remainder_lt' (n : ℕ) {m : ℝ} (m1 : 1 < m) :
    remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        (remainder_summable m1 n)
        (summable_one_div_pow_of_le m1 fun _ => le_self_add)
    _ = ∑' i : ℕ, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]
theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) :
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n !) ^ n :=
  calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :=
      mul_le_mul_of_nonneg_right (sub_one_div_inv_le_two hm) (by positivity)
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ ≤ 1 / m ^ (n ! * n) := by
      apply (div_le_div_iff₀ _ _).mpr
      focus
        conv_rhs => rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul]
        refine (mul_le_mul_right ?_).mpr ?_
      any_goals exact pow_pos (zero_lt_two.trans_le hm) _
      exact _root_.trans (_root_.trans hm (pow_one _).symm.le)
        (pow_right_mono₀ (one_le_two.trans hm) n.factorial_pos)
    _ = 1 / (m ^ n !) ^ n := congr_arg (1 / ·) (pow_mul m n ! n)
theorem remainder_lt (n : ℕ) {m : ℝ} (m2 : 2 ≤ m) : remainder m n < 1 / (m ^ n !) ^ n :=
  (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)
theorem partialSum_eq_rat {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : ℕ, partialSum m k = p / ((m ^ k ! :) : ℝ) := by
  induction' k with k h
  · exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  · rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ, h_k, div_add_div, div_eq_div_iff, add_mul]
    · norm_cast
      rw [add_mul, one_mul, Nat.factorial_succ, add_mul, one_mul, add_tsub_cancel_right, pow_add]
      simp [mul_assoc]
    all_goals positivity
end LiouvilleNumber
open LiouvilleNumber
theorem liouville_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) : Liouville (liouvilleNumber m) := by
  have mZ1 : 1 < (m : ℤ) := by norm_cast
  have m1 : 1 < (m : ℝ) := by norm_cast
  intro n
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow₀ mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  rw [← partialSum_add_remainder m1 n, ← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)
theorem transcendental_liouvilleNumber {m : ℕ} (hm : 2 ≤ m) :
    Transcendental ℤ (liouvilleNumber m) :=
  (liouville_liouvilleNumber hm).transcendental