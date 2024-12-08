import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Polynomial.Basic
namespace MvPolynomial
variable {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (h : ∀ x : Fin n → R, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    rw [RingEquiv.map_zero]
    convert h finZeroElim
  | succ n ih =>
    apply (finSuccEquiv R n).injective
    simp only [map_zero]
    refine Polynomial.funext fun q => ?_
    rw [Polynomial.eval_zero]
    apply ih fun x => ?_
    calc _ = _ := eval_polynomial_eval_finSuccEquiv p _
         _ = 0 := h _
theorem funext {σ : Type*} {p q : MvPolynomial σ R} (h : ∀ x : σ → R, eval x p = eval x q) :
    p = q := by
  suffices ∀ p, (∀ x : σ → R, eval x p = 0) → p = 0 by
    rw [← sub_eq_zero, this (p - q)]
    simp only [h, RingHom.map_sub, forall_const, sub_self]
  clear h p q
  intro p h
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  suffices p = 0 by rw [this, map_zero]
  apply funext_fin
  intro x
  classical
    convert h (Function.extend f x 0)
    simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
theorem funext_iff {σ : Type*} {p q : MvPolynomial σ R} :
    p = q ↔ ∀ x : σ → R, eval x p = eval x q :=
  ⟨by rintro rfl; simp only [forall_const, eq_self_iff_true], funext⟩
end MvPolynomial