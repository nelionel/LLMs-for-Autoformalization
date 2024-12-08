import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open Matrix
namespace Matrix
open Equiv Finset
variable {R S : Type*} [CommRing R] [Nontrivial R] [LinearOrderedCommRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem det_le {A : Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
    abv A.det ≤ Nat.factorial (Fintype.card n) • x ^ Fintype.card n :=
  calc
    abv A.det = abv (∑ σ : Perm n, Perm.sign σ • ∏ i, A (σ i) i) := congr_arg abv (det_apply _)
    _ ≤ ∑ σ : Perm n, abv (Perm.sign σ • ∏ i, A (σ i) i) := abv.sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, abv (A (σ i) i) :=
      (sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod])
    _ ≤ ∑ _σ : Perm n, ∏ _i : n, x :=
      (sum_le_sum fun _ _ => prod_le_prod (fun _ _ => abv.nonneg _) fun _ _ => hx _ _)
    _ = ∑ _σ : Perm n, x ^ Fintype.card n :=
      (sum_congr rfl fun _ _ => by rw [prod_const, Finset.card_univ])
    _ = Nat.factorial (Fintype.card n) • x ^ Fintype.card n := by
      rw [sum_const, Finset.card_univ, Fintype.card_perm]
theorem det_sum_le {ι : Type*} (s : Finset ι) {A : ι → Matrix n n R} {abv : AbsoluteValue R S}
    {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) :
    abv (det (∑ k ∈ s, A k)) ≤
      Nat.factorial (Fintype.card n) • (#s• x) ^ Fintype.card n :=
  det_le fun i j =>
    calc
      abv ((∑ k ∈ s, A k) i j) = abv (∑ k ∈ s, A k i j) := by simp only [sum_apply]
      _ ≤ ∑ k ∈ s, abv (A k i j) := abv.sum_le _ _
      _ ≤ ∑ _k ∈ s, x := sum_le_sum fun k _ => hx k i j
      _ = #s • x := sum_const _
theorem det_sum_smul_le {ι : Type*} (s : Finset ι) {c : ι → R} {A : ι → Matrix n n R}
    {abv : AbsoluteValue R S} {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) {y : S}
    (hy : ∀ k, abv (c k) ≤ y) :
    abv (det (∑ k ∈ s, c k • A k)) ≤
      Nat.factorial (Fintype.card n) • (#s • y * x) ^ Fintype.card n := by
  simpa only [smul_mul_assoc] using
    det_sum_le s fun k i j =>
      calc
        abv (c k * A k i j) = abv (c k) * abv (A k i j) := abv.map_mul _ _
        _ ≤ y * x := mul_le_mul (hy k) (hx k i j) (abv.nonneg _) ((abv.nonneg _).trans (hy k))
end Matrix