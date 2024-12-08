import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Embeddings
universe u
namespace IsCyclotomicExtension.Rat
open NumberField InfinitePlace Module Complex Nat Polynomial
variable {n : ℕ+} (K : Type u) [Field K] [CharZero K]
theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn
variable (n)
theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn, zero_add, IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat n.pos), hk, ← two_mul, Nat.mul_right_inj (by norm_num)] at key
    simp [hk, key, ← two_mul]
  · have : φ n = 1 := by
      by_cases h1 : 1 < n.1
      · convert totient_two
        exact (eq_of_le_of_not_lt (succ_le_of_lt h1) hn).symm
      · convert totient_one
        rw [← PNat.one_coe, PNat.coe_inj]
        exact eq_of_le_of_not_lt (not_lt.mp h1) (PNat.not_lt_one _)
    rw [this]
    apply nrComplexPlaces_eq_zero_of_finrank_eq_one
    rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat n.pos), this]
end IsCyclotomicExtension.Rat