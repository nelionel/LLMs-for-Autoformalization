import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
universe u v
noncomputable section
namespace MvPolynomial
open DirectSum TensorProduct
open Set LinearMap Submodule
variable {R : Type u} {N : Type v} [CommSemiring R]
variable {σ : Type*}
variable {S : Type*} [CommSemiring S] [Algebra R S]
section Module
variable [DecidableEq σ]
variable [AddCommMonoid N] [Module R N]
noncomputable def rTensor :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft' _ _ _ _ _
lemma rTensor_apply_tmul (p : MvPolynomial σ S) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n
lemma rTensor_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d
lemma rTensor_apply_monomial_tmul (e : σ →₀ ℕ) (s : S) (n : N) (d : σ →₀ ℕ) :
    rTensor (monomial e s ⊗ₜ[R] n) d = if e = d then s ⊗ₜ[R] n else 0 := by
  simp only [rTensor_apply_tmul_apply, coeff_monomial, ite_tmul]
lemma rTensor_apply_X_tmul (s : σ) (n : N) (d : σ →₀ ℕ) :
    rTensor (X s ⊗ₜ[R] n) d = if Finsupp.single s 1 = d then (1 : S) ⊗ₜ[R] n else 0 := by
  rw [rTensor_apply_tmul_apply, coeff_X', ite_tmul]
lemma rTensor_apply (t : MvPolynomial σ S ⊗[R] N) (d : σ →₀ ℕ) :
    rTensor t d = ((lcoeff S d).restrictScalars R).rTensor N t :=
  TensorProduct.finsuppLeft_apply t d
@[simp]
lemma rTensor_symm_apply_single (d : σ →₀ ℕ) (s : S) (n : N) :
    rTensor.symm (Finsupp.single d (s ⊗ₜ n)) =
      (monomial d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single (R := R) d s n
noncomputable def scalarRTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft _ _ _
lemma scalarRTensor_apply_tmul (p : MvPolynomial σ R) (n : N) :
    scalarRTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n
lemma scalarRTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N) (d : σ →₀ ℕ) :
    scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d
lemma scalarRTensor_apply_monomial_tmul (e : σ →₀ ℕ) (r : R) (n : N) (d : σ →₀ ℕ) :
    scalarRTensor (monomial e r ⊗ₜ[R] n) d = if e = d then r • n else 0 := by
  rw [scalarRTensor_apply_tmul_apply, coeff_monomial, ite_smul, zero_smul]
lemma scalarRTensor_apply_X_tmul_apply (s : σ) (n : N) (d : σ →₀ ℕ) :
    scalarRTensor (X s ⊗ₜ[R] n) d = if Finsupp.single s 1 = d then n else 0 := by
  rw [scalarRTensor_apply_tmul_apply, coeff_X', ite_smul, one_smul, zero_smul]
lemma scalarRTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    scalarRTensor.symm (Finsupp.single d n) = (monomial d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n
end Module
section Algebra
variable [CommSemiring N] [Algebra R N]
noncomputable def rTensorAlgHom :
    (MvPolynomial σ S) ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp [commute_iff_eq, algebraMap_eq, mul_comm])
@[simp]
lemma coeff_rTensorAlgHom_tmul
    (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgHom (p ⊗ₜ[R] n)) = (coeff d p) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [algebraMap_eq, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]
section DecidableEq
variable [DecidableEq σ]
lemma coeff_rTensorAlgHom_monomial_tmul
    (e : σ →₀ ℕ) (s : S) (n : N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgHom (monomial e s ⊗ₜ[R] n)) =
      if e = d then s ⊗ₜ[R] n else 0 := by
  simp [ite_tmul]
lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MvPolynomial σ S ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N)).toLinearMap =
      rTensor.toLinearMap := by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  rw [coeff_rTensorAlgHom_tmul]
  simp only [coeff]
  erw [finsuppLeft_apply_tmul_apply]
lemma rTensorAlgHom_apply_eq (p : MvPolynomial σ S ⊗[R] N) :
    rTensorAlgHom (S := S) p = rTensor p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl
noncomputable def rTensorAlgEquiv :
    (MvPolynomial σ S) ⊗[R] N ≃ₐ[S] MvPolynomial σ (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv rTensor
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    exact finsuppLeft_symm_apply_single (R := R) (0 : σ →₀ ℕ) (1 : S) (1 : N)
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]
    rfl
noncomputable def scalarRTensorAlgEquiv :
    MvPolynomial σ R ⊗[R] N ≃ₐ[R] MvPolynomial σ N :=
  rTensorAlgEquiv.trans (mapAlgEquiv σ (Algebra.TensorProduct.lid R N))
end DecidableEq
variable (R)
variable (A : Type*) [CommSemiring A] [Algebra R A]
noncomputable def algebraTensorAlgEquiv :
    A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A := AlgEquiv.ofAlgHom
  (Algebra.TensorProduct.lift
    (Algebra.ofId A (MvPolynomial σ A))
    (MvPolynomial.mapAlgHom <| Algebra.ofId R A) (fun _ _ ↦ Commute.all _ _))
  (aeval (fun s ↦ 1 ⊗ₜ X s))
  (by ext s; simp)
  (by ext s; simp)
@[simp]
lemma algebraTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) :
    algebraTensorAlgEquiv R A (a ⊗ₜ p) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [algebraTensorAlgEquiv, Algebra.smul_def]
  rfl
@[simp]
lemma algebraTensorAlgEquiv_symm_X (s : σ) :
    (algebraTensorAlgEquiv R A).symm (X s) = 1 ⊗ₜ X s := by
  simp [algebraTensorAlgEquiv]
@[simp]
lemma algebraTensorAlgEquiv_symm_monomial (m : σ →₀ ℕ) (a : A) :
    (algebraTensorAlgEquiv R A).symm (monomial m a) = a ⊗ₜ monomial m 1 := by
  apply @Finsupp.induction σ ℕ _ _ m
  · simp [algebraTensorAlgEquiv]
  · intro i n f _ _ hfa
    simp only [algebraTensorAlgEquiv, AlgEquiv.ofAlgHom_symm_apply] at hfa ⊢
    simp only [add_comm, monomial_add_single, _root_.map_mul, map_pow, aeval_X,
      Algebra.TensorProduct.tmul_pow, one_pow, hfa]
    nth_rw 2 [← mul_one a]
    rw [Algebra.TensorProduct.tmul_mul_tmul]
lemma aeval_one_tmul (f : σ → S) (p : MvPolynomial σ R) :
    (aeval fun x ↦ (1 ⊗ₜ[R] f x : N ⊗[R] S)) p = 1 ⊗ₜ[R] (aeval f) p := by
  induction' p using MvPolynomial.induction_on with a p q hp hq p i h
  · simp only [map_C, algHom_C, Algebra.TensorProduct.algebraMap_apply,
      RingHomCompTriple.comp_apply]
    rw [← mul_one ((algebraMap R N) a), ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]
  · simp [hp, hq, tmul_add]
  · simp [h]
end Algebra
end MvPolynomial
end