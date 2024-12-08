import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivation
open scoped TensorProduct
open Algebra
universe u v
variable (R : Type u) [CommRing R]
suppress_compilation
section MvPolynomial
def KaehlerDifferential.mvPolynomialEquiv (σ : Type*) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ →₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x ↦ D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | h0 => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | hadd => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | hsingle a b => simp [LinearMap.map_smul, -map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | h0 =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero, map_zero, map_zero]
    | hadd => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | hsingle a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]
def KaehlerDifferential.mvPolynomialBasis (σ) :
    Basis σ (MvPolynomial σ R) (Ω[MvPolynomial σ R⁄R]) :=
  ⟨mvPolynomialEquiv R σ⟩
lemma KaehlerDifferential.mvPolynomialBasis_repr_comp_D (σ) :
    (mvPolynomialBasis R σ).repr.toLinearMap.compDer (D _ _) =
      MvPolynomial.mkDerivation _ (Finsupp.single · 1) :=
  Derivation.liftKaehlerDifferential_comp _
lemma KaehlerDifferential.mvPolynomialBasis_repr_D (σ) (x) :
    (mvPolynomialBasis R σ).repr (D _ _ x) =
      MvPolynomial.mkDerivation R (Finsupp.single · (1 : MvPolynomial σ R)) x :=
  Derivation.congr_fun (mvPolynomialBasis_repr_comp_D R σ) x
@[simp]
lemma KaehlerDifferential.mvPolynomialBasis_repr_D_X (σ) (i) :
    (mvPolynomialBasis R σ).repr (D _ _ (.X i)) = Finsupp.single i 1 := by
  simp [mvPolynomialBasis_repr_D]
@[simp]
lemma KaehlerDifferential.mvPolynomialBasis_repr_apply (σ) (x) (i) :
    (mvPolynomialBasis R σ).repr (D _ _ x) i = MvPolynomial.pderiv i x := by
  classical
  suffices ((Finsupp.lapply i).comp
    (mvPolynomialBasis R σ).repr.toLinearMap).compDer (D _ _) = MvPolynomial.pderiv i by
    rw [← this]; rfl
  apply MvPolynomial.derivation_ext
  intro j
  simp [Finsupp.single_apply, Pi.single_apply]
lemma KaehlerDifferential.mvPolynomialBasis_repr_symm_single (σ) (i) (x) :
    (mvPolynomialBasis R σ).repr.symm (Finsupp.single i x) = x • D R (MvPolynomial σ R) (.X i) := by
  apply (mvPolynomialBasis R σ).repr.injective; simp [LinearEquiv.map_smul, -map_smul]
@[simp]
lemma KaehlerDifferential.mvPolynomialBasis_apply (σ) (i) :
    mvPolynomialBasis R σ i = D R (MvPolynomial σ R) (.X i) :=
  (mvPolynomialBasis_repr_symm_single R σ i 1).trans (one_smul _ _)
instance (σ) : Module.Free (MvPolynomial σ R) (Ω[MvPolynomial σ R⁄R]) :=
  .of_basis (KaehlerDifferential.mvPolynomialBasis R σ)
end MvPolynomial
section Polynomial
open Polynomial
lemma KaehlerDifferential.polynomial_D_apply (P : R[X]) :
    D R R[X] P = derivative P • D R R[X] X := by
  rw [← aeval_X_left_apply P, (D R R[X]).map_aeval, aeval_X_left_apply, aeval_X_left_apply]
def KaehlerDifferential.polynomialEquiv : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where
  __ := derivative'.liftKaehlerDifferential
  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction' x using Finsupp.induction_linear with x y hx hy x y
    · simp
    · simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.flip_apply,
        AlgHom.toLinearMap_apply, lsmul_coe] at *; simp only [*]
    · simp [polynomial_D_apply _ x]
  right_inv x := by simp
lemma KaehlerDifferential.polynomialEquiv_comp_D :
    (polynomialEquiv R).compDer (D R R[X]) = derivative' :=
  Derivation.liftKaehlerDifferential_comp _
@[simp]
lemma KaehlerDifferential.polynomialEquiv_D (P) :
    polynomialEquiv R (D R R[X] P) = derivative P :=
  Derivation.congr_fun (polynomialEquiv_comp_D R) P
@[simp]
lemma KaehlerDifferential.polynomialEquiv_symm (P) :
    (polynomialEquiv R).symm P = P • D R R[X] X := rfl
end Polynomial