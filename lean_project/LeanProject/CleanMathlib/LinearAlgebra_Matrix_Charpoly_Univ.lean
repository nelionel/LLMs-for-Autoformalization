import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.MvPolynomial.Homogeneous
namespace Matrix.charpoly
variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
variable (f : R →+* S)
variable (R)
noncomputable
abbrev univ : Polynomial (MvPolynomial (n × n) R) :=
  charpoly <| mvPolynomialX n n R
variable {R}
open MvPolynomial RingHomClass in
@[simp]
lemma univ_map_eval₂Hom (M : n × n → S) :
    (univ R n).map (eval₂Hom f M) = charpoly (Matrix.of M.curry) := by
  rw [univ, ← charpoly_map, coe_eval₂Hom, ← mvPolynomialX_map_eval₂ f (Matrix.of M.curry)]
  simp only [of_apply, Function.curry_apply, Prod.mk.eta]
lemma univ_map_map :
    (univ R n).map (MvPolynomial.map f) = univ S n := by
  rw [MvPolynomial.map, univ_map_eval₂Hom]; rfl
@[simp]
lemma univ_coeff_eval₂Hom (M : n × n → S) (i : ℕ) :
    MvPolynomial.eval₂Hom f M ((univ R n).coeff i) =
      (charpoly (Matrix.of M.curry)).coeff i := by
  rw [← univ_map_eval₂Hom n f M, Polynomial.coeff_map]
variable (R)
lemma univ_monic : (univ R n).Monic := charpoly_monic (mvPolynomialX n n R)
lemma univ_natDegree [Nontrivial R] : (univ R n).natDegree = Fintype.card n :=
  charpoly_natDegree_eq_dim (mvPolynomialX n n R)
@[simp]
lemma univ_coeff_card : (univ R n).coeff (Fintype.card n) = 1 := by
  suffices Polynomial.coeff (univ ℤ n) (Fintype.card n) = 1 by
    rw [← univ_map_map n (Int.castRingHom R), Polynomial.coeff_map, this, _root_.map_one]
  rw [← univ_natDegree ℤ n]
  exact (univ_monic ℤ n).leadingCoeff
open MvPolynomial in
lemma optionEquivLeft_symm_univ_isHomogeneous :
    ((optionEquivLeft R (n × n)).symm (univ R n)).IsHomogeneous (Fintype.card n) := by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, univ, charpoly, charmatrix, scalar_apply, RingHom.mapMatrix_apply, det_apply',
    sub_apply, map_apply, of_apply, map_sum, _root_.map_mul, map_intCast, map_prod, map_sub,
    optionEquivLeft_symm_apply, Polynomial.aevalTower_C, rename_X, diagonal, mvPolynomialX]
  apply IsHomogeneous.sum
  rintro i -
  apply IsHomogeneous.mul
  · apply isHomogeneous_C
  · apply IsHomogeneous.prod
    rintro j -
    by_cases h : i j = j
    · simp only [h, ↓reduceIte, Polynomial.aevalTower_X, IsHomogeneous.sub, isHomogeneous_X]
    · simp only [h, ↓reduceIte, map_zero, zero_sub, (isHomogeneous_X _ _).neg]
lemma univ_coeff_isHomogeneous (i j : ℕ) (h : i + j = Fintype.card n) :
    ((univ R n).coeff i).IsHomogeneous j :=
  (optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h
end Matrix.charpoly