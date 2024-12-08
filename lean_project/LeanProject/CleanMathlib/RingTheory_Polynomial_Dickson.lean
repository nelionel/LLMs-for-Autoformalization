import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Roots
noncomputable section
namespace Polynomial
variable {R S : Type*} [CommRing R] [CommRing S] (k : ℕ) (a : R)
noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n
@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl
@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl
theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X]) := by
  simp only [dickson, sq]
@[simp]
theorem dickson_add_two (n : ℕ) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]
theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n
variable {k a}
theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp_rw [dickson_zero, Polynomial.map_sub, Polynomial.map_natCast, Polynomial.map_ofNat]
  | 1 => by simp only [dickson_one, map_X]
  | n + 2 => by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    rw [map_dickson f n, map_dickson f (n + 1)]
@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    norm_num
  | 1 => by simp only [dickson_one, pow_one]
  | n + 2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero (n + 1), pow_add X (n + 1) 1, mul_comm, pow_one]
section Dickson
theorem dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
    ∀ n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by
    simp only [eval_one, eval_add, pow_zero, dickson_zero]; norm_num
  | 1 => by simp only [eval_X, dickson_one, pow_one]
  | n + 2 => by
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv x y h _, eval_X, dickson_add_two,
      C_1, eval_one]
    conv_lhs => simp only [pow_succ', add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul]
    ring
variable (R)
private theorem two_mul_C_half_eq_one [Invertible (2 : R)] : 2 * C (⅟ 2 : R) = 1 := by
  rw [two_mul, ← C_add, invOf_two_add_invOf_two, C_1]
private theorem C_half_mul_two_eq_one [Invertible (2 : R)] : C (⅟ 2 : R) * 2 = 1 := by
  rw [mul_comm, two_mul_C_half_eq_one]
theorem dickson_one_one_eq_chebyshev_C : ∀ n, dickson 1 (1 : R) n = Chebyshev.C R n
  | 0 => by
    simp only [Chebyshev.C_zero, mul_one, one_comp, dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, Nat.cast_one, Chebyshev.C_one]
  | n + 2 => by
    rw [dickson_add_two, C_1, Nat.cast_add, Nat.cast_two, Chebyshev.C_add_two,
      dickson_one_one_eq_chebyshev_C (n + 1), dickson_one_one_eq_chebyshev_C n]
    push_cast
    ring
theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] (n : ℕ) :
    dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟ 2) * X) :=
  (dickson_one_one_eq_chebyshev_C R n).trans (Chebyshev.C_eq_two_mul_T_comp_half_mul_X R n)
theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
    Chebyshev.T R n = C (⅟ 2) * (dickson 1 1 n).comp (2 * X) :=
  dickson_one_one_eq_chebyshev_C R n ▸ Chebyshev.T_eq_half_mul_C_comp_two_mul_X R n
theorem dickson_two_one_eq_chebyshev_S : ∀ n, dickson 2 (1 : R) n = Chebyshev.S R n
  | 0 => by
    simp only [Chebyshev.S_zero, mul_one, one_comp, dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, Nat.cast_one, Chebyshev.S_one]
  | n + 2 => by
    rw [dickson_add_two, C_1, Nat.cast_add, Nat.cast_two, Chebyshev.S_add_two,
      dickson_two_one_eq_chebyshev_S (n + 1), dickson_two_one_eq_chebyshev_S n]
    push_cast
    ring
theorem dickson_two_one_eq_chebyshev_U [Invertible (2 : R)] (n : ℕ) :
    dickson 2 (1 : R) n = (Chebyshev.U R n).comp (C (⅟ 2) * X) :=
  (dickson_two_one_eq_chebyshev_S R n).trans (Chebyshev.S_eq_U_comp_half_mul_X R n)
theorem chebyshev_U_eq_dickson_two_one (n : ℕ) :
    Chebyshev.U R n = (dickson 2 (1 : R) n).comp (2 * X) :=
  dickson_two_one_eq_chebyshev_S R n ▸ (Chebyshev.S_comp_two_mul_X R n).symm
theorem dickson_one_one_mul (m n : ℕ) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) := by
  have h : (1 : R) = Int.castRingHom R 1 := by simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_one_one_eq_chebyshev_T,
    Nat.cast_mul, Chebyshev.T_mul, two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  apply eval₂_congr rfl rfl
  rw [comp_assoc]
  apply eval₂_congr rfl _ rfl
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, C_half_mul_two_eq_one, one_mul]
theorem dickson_one_one_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul, mul_comm, dickson_one_one_mul]
theorem dickson_one_one_zmod_p (p : ℕ) [Fact p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p := by
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type) (_ : Field K), ∃ _ : CharP K p, Infinite K := by
    let K := FractionRing (Polynomial (ZMod p))
    let f : ZMod p →+* K := (algebraMap _ (FractionRing _)).comp C
    have : CharP K p := by
      rw [← f.charP_iff_charP]
      infer_instance
    haveI : Infinite K :=
      Infinite.of_injective (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        (IsFractionRing.injective _ _)
    refine ⟨K, ?_, ?_, ?_⟩ <;> infer_instance
  apply map_injective (ZMod.castHom (dvd_refl p) K) (RingHom.injective _)
  rw [map_dickson, Polynomial.map_pow, map_X]
  apply eq_of_infinite_eval_eq
  apply @Set.Infinite.mono _ { x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0 }
  · rintro _ ⟨x, rfl, hx⟩
    simp only [eval_X, eval_pow, Set.mem_setOf_eq, ZMod.cast_one', add_pow_char,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ hx), ZMod.castHom_apply]
  · intro h
    rw [← Set.infinite_univ_iff] at H
    apply H
    suffices (Set.univ : Set K) =
        ⋃ x ∈ { x : K | ∃ y : K, x = y + y⁻¹ ∧ y ≠ 0 }, { y | x = y + y⁻¹ ∨ y = 0 }  by
      rw [this]
      clear this
      refine h.biUnion fun x _ => ?_
      let φ : K[X] := X ^ 2 - C x * X + 1
      have hφ : φ ≠ 0 := by
        intro H
        have : φ.eval 0 = 0 := by rw [H, eval_zero]
        simpa [φ, eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add, eval_mul,
          mul_zero, sq, zero_add, one_ne_zero]
      classical
        convert (φ.roots ∪ {0}).toFinset.finite_toSet using 1
        ext1 y
        simp only [φ, Multiset.mem_toFinset, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_union,
          mem_roots hφ, IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          Multiset.mem_singleton]
        by_cases hy : y = 0
        · simp only [hy, eq_self_iff_true, or_true]
        apply or_congr _ Iff.rfl
        rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel₀ hy]
        apply eq_iff_eq_cancel_right.mpr
        ring
    apply (Set.eq_univ_of_forall _).symm
    intro x
    simp only [exists_prop, Set.mem_iUnion, Ne, Set.mem_setOf_eq]
    by_cases hx : x = 0
    · simp only [hx, and_true, eq_self_iff_true, inv_zero, or_true]
      exact ⟨_, 1, rfl, one_ne_zero⟩
    · simp only [hx, or_false, exists_eq_right]
      exact ⟨_, rfl, hx⟩
theorem dickson_one_one_charP (p : ℕ) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p := by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h, ← map_dickson (ZMod.castHom (dvd_refl p) R), dickson_one_one_zmod_p, Polynomial.map_pow,
    map_X]
end Dickson
end Polynomial