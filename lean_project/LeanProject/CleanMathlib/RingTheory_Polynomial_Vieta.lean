import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
open Finset Polynomial
namespace Multiset
section Semiring
variable {R : Type*} [CommSemiring R]
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1), (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  classical
    rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len,
      map_bind, sum_bind, Finset.sum_eq_multiset_sum, Finset.range_val, map_congr (Eq.refl _)]
    intro _ _
    rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
    intro s ht
    rw [mem_powersetCard] at ht
    dsimp
    rw [prod_hom' s (Polynomial.C : R →+* R[X])]
    simp [ht, map_const, prod_replicate, prod_hom', map_id', card_sub]
theorem prod_X_add_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun r => X + C r).prod.coeff k = s.esymm (Multiset.card s - k) := by
  convert Polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k using 1
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (Multiset.card s - k) _]
  · rw [if_pos (Nat.sub_sub_self h).symm]
  · intro j hj1 hj2
    suffices k ≠ card s - j by rw [if_neg this]
    intro hn
    rw [hn, Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj1))] at hj2
    exact Ne.irrefl hj2
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.sub_le (Multiset.card s) k)
theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun i => X + C (r i)).prod.coeff k = (s.map r).esymm (Multiset.card s - k) := by
  erw [← map_map (fun r => X + C r) r, prod_X_add_C_coeff] <;> rw [s.card_map r]; assumption
theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ #s) :
    (∏ i ∈ s, (X + C (r i))).coeff k = ∑ t ∈ s.powersetCard (#s - k), ∏ i ∈ t, r i := by
  rw [Finset.prod, prod_X_add_C_coeff' _ r h, Finset.esymm_map_val]
  rfl
end Semiring
section Ring
variable {R : Type*} [CommRing R]
theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k := by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powersetCard_map, Multiset.map_map,
    map_congr rfl]
  intro x hx
  rw [(mem_powersetCard.mp hx).right.symm, ← prod_replicate, ← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul, map_congr rfl, Function.comp_apply]
  exact fun z _ => neg_one_mul z
theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1),
        (-1) ^ j * (C (s.esymm j) * X ^ (Multiset.card s - j)) := by
  conv_lhs =>
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rw [map_map]; rfl
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) :
    (s.map fun t => X - C t).prod.coeff k =
    (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) := by
  conv_lhs =>
    congr
    congr
    congr
    ext x
    rw [sub_eq_add_neg]
    rw [← map_neg C x]
  convert prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rw [map_map]; rfl
  · rw [esymm_neg, card_map]
  · rwa [card_map]
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul, mul_assoc]; congr
  have : k ≤ card (roots p) := by rw [hroots]; exact h
  convert p.roots.prod_X_sub_C_coeff this using 3 <;> rw [hroots]
theorem _root_.Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
    (hsplit : p.Splits (RingHom.id F)) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h
end Ring
end Multiset
section MvPolynomial
open Finset Polynomial Fintype
variable (R σ : Type*) [CommSemiring R] [Fintype σ]
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i))) =
      ∑ j ∈ range (card σ + 1), Polynomial.C
        (MvPolynomial.esymm σ R j) * Polynomial.X ^ (card σ - j) := by
  let s := Finset.univ.val.map fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  simp_rw [this, MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert Multiset.prod_X_add_C_eq_sum_esymm s
  simp_rw [s, Multiset.map_map, Function.comp_apply]
theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, (Polynomial.X + Polynomial.C (MvPolynomial.X i)) : Polynomial _).coeff k =
    MvPolynomial.esymm σ R (card σ - k) := by
  let s := Finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  have : Fintype.card σ = Multiset.card s := by
    rw [Multiset.card_map, ← Finset.card_univ, Finset.card_def]
  rw [this] at h ⊢
  rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
  convert Multiset.prod_X_add_C_coeff s h
  dsimp
  simp_rw [s, Multiset.map_map, Function.comp_apply]
end MvPolynomial