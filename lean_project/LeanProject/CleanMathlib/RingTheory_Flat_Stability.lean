import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
universe u v w t
open Function (Injective Surjective)
open LinearMap (lsmul rTensor lTensor)
open TensorProduct
namespace Module.Flat
section Composition
variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
private noncomputable abbrev auxRightMul (I : Ideal R) : M ⊗[R] I →ₗ[S] M := by
  letI i : M ⊗[R] I →ₗ[S] M ⊗[R] R := AlgebraTensorModule.map LinearMap.id I.subtype
  letI e' : M ⊗[R] R →ₗ[S] M := AlgebraTensorModule.rid R S M
  exact AlgebraTensorModule.rid R S M ∘ₗ i
private noncomputable abbrev J (I : Ideal R) : Ideal S := LinearMap.range (auxRightMul R S S I)
private noncomputable abbrev auxIso [Flat R S] {I : Ideal R} :
    S ⊗[R] I ≃ₗ[S] J R S I := by
  apply LinearEquiv.ofInjective (auxRightMul R S S I)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  exact (Flat.iff_lTensor_injective' R S).mp inferInstance I
private noncomputable abbrev auxLTensor [Flat R S] (I : Ideal R) :
    M ⊗[R] I →ₗ[S] M := by
  letI e1 : M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I) :=
    (AlgebraTensorModule.cancelBaseChange R S S M I).symm
  letI e2 : M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[S] (J R S I) :=
    TensorProduct.congr (LinearEquiv.refl S M) (auxIso R S)
  letI e3 : M ⊗[S] (J R S I) →ₗ[S] M ⊗[S] S := lTensor M (J R S I).subtype
  letI e4 : M ⊗[S] S →ₗ[S] M := TensorProduct.rid S M
  exact e4 ∘ₗ e3 ∘ₗ (e1 ≪≫ₗ e2)
private lemma auxLTensor_eq [Flat R S] {I : Ideal R} :
    (auxLTensor R S M I : M ⊗[R] I →ₗ[R] M) =
    TensorProduct.rid R M ∘ₗ lTensor M I.subtype := by
  apply TensorProduct.ext'
  intro m x
  erw [TensorProduct.rid_tmul]
  simp
theorem trans [Flat R S] [Flat S M] : Flat R M := by
  rw [Flat.iff_lTensor_injective']
  intro I
  rw [← EquivLike.comp_injective _ (TensorProduct.rid R M)]
  haveI h : TensorProduct.rid R M ∘ lTensor M I.subtype =
    TensorProduct.rid R M ∘ₗ lTensor M I.subtype := rfl
  simp only [h, ← auxLTensor_eq R S M, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
  exact (Flat.iff_lTensor_injective' S M).mp inferInstance _
@[deprecated (since := "2024-11-03")] alias comp := trans
end Composition
section BaseChange
variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
private noncomputable abbrev auxRTensorBaseChange (I : Ideal S) :
    I ⊗[S] (S ⊗[R] M) →ₗ[S] S ⊗[S] (S ⊗[R] M) :=
  letI e1 : I ⊗[S] (S ⊗[R] M) ≃ₗ[S] I ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S S I M
  letI e2 : S ⊗[S] (S ⊗[R] M) ≃ₗ[S] S ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S S S M
  letI f : I ⊗[R] M →ₗ[S] S ⊗[R] M := AlgebraTensorModule.map I.subtype LinearMap.id
  e2.symm.toLinearMap ∘ₗ f ∘ₗ e1.toLinearMap
private lemma auxRTensorBaseChange_eq (I : Ideal S) :
    auxRTensorBaseChange R S M I = rTensor (S ⊗[R] M) I.subtype := by
  ext
  simp
instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := by
  rw [Flat.iff_rTensor_injective']
  intro I
  simp only [← auxRTensorBaseChange_eq, auxRTensorBaseChange, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact rTensor_preserves_injective_linearMap (I.subtype : I →ₗ[R] S) Subtype.val_injective
theorem isBaseChange [Flat R M] (N : Type t) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Flat S N :=
  of_linearEquiv S (S ⊗[R] M) N (IsBaseChange.equiv h).symm
end BaseChange
section Localization
variable {R : Type u} {M Mp : Type*} (Rp : Type v)
  [CommRing R] [AddCommGroup M] [Module R M] [CommRing Rp] [Algebra R Rp]
  [AddCommGroup Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]
instance localizedModule [Flat R M] (S : Submonoid R) :
    Flat (Localization S) (LocalizedModule S M) := by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S
theorem of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp := by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h
end Localization
end Module.Flat