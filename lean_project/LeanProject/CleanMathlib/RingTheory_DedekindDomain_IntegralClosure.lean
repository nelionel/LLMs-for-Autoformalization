import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Trace.Basic
variable (A K : Type*) [CommRing A] [Field K]
open scoped nonZeroDivisors Polynomial
section IsIntegralClosure
open Algebra
variable [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] (C : Type*) [CommRing C]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
include K L
theorem IsIntegralClosure.isLocalization [IsDomain A] [Algebra.IsAlgebraic K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L := by
  haveI : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI : NoZeroSMulDivisors A L := NoZeroSMulDivisors.trans A K L
  haveI : NoZeroSMulDivisors A C := IsIntegralClosure.noZeroSMulDivisors A L
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    rw [isUnit_iff_ne_zero, map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective C A L),
      Subtype.coe_mk, map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective A C)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx
  · obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z
        (Algebra.IsIntegral.isIntegral (R := K) z)
    obtain ⟨x, hx⟩ : ∃ x, algebraMap C L x = m • z := IsIntegralClosure.isIntegral_iff.mp hm
    refine ⟨⟨x, algebraMap A C m, m, SetLike.coe_mem m, rfl⟩, ?_⟩
    rw [Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, hx, mul_comm, Submonoid.smul_def,
      smul_def]
  · simp only [IsIntegralClosure.algebraMap_injective C A L h]
theorem IsIntegralClosure.isLocalization_of_isSeparable [IsDomain A] [Algebra.IsSeparable K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
  IsIntegralClosure.isLocalization A K L C
variable [FiniteDimensional K L]
variable {A K L}
theorem IsIntegralClosure.range_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    LinearMap.range ((Algebra.linearMap C L).restrictScalars A) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis,
    ← LinearMap.BilinForm.le_flip_dualSubmodule, Submodule.span_le]
  rintro _ ⟨i, rfl⟩ _ ⟨y, rfl⟩
  simp only [LinearMap.coe_restrictScalars, linearMap_apply, LinearMap.BilinForm.flip_apply,
    traceForm_apply]
  refine Submodule.mem_one.mpr <| IsIntegrallyClosed.isIntegral_iff.mp ?_
  exact isIntegral_trace ((IsIntegralClosure.isIntegral A L y).algebraMap.mul (hb_int i))
theorem integralClosure_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    Subalgebra.toSubmodule (integralClosure A L) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  refine le_trans ?_ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩
variable [IsDomain A]
variable (A K)
theorem exists_integral_multiples (s : Finset L) :
    ∃ y ≠ (0 : A), ∀ x ∈ s, IsIntegral A (y • x) := by
  haveI := Classical.decEq L
  refine s.induction ?_ ?_
  · use 1, one_ne_zero
    rintro x ⟨⟩
  · rintro x s hx ⟨y, hy, hs⟩
    have := exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff A K L).mpr (.of_finite _ x))
      ((injective_iff_map_eq_zero (algebraMap A L)).mp ?_)
    · rcases this with ⟨x', y', hy', hx'⟩
      refine ⟨y * y', mul_ne_zero hy hy', fun x'' hx'' => ?_⟩
      rcases Finset.mem_insert.mp hx'' with (rfl | hx'')
      · rw [mul_smul, Algebra.smul_def, Algebra.smul_def, hx']
        exact isIntegral_algebraMap.mul x'.2
      · rw [mul_comm, mul_smul, Algebra.smul_def]
        exact isIntegral_algebraMap.mul (hs _ hx'')
    · rw [IsScalarTower.algebraMap_eq A K L]
      apply (algebraMap K L).injective.comp
      exact IsFractionRing.injective _ _
variable (L)
theorem FiniteDimensional.exists_is_basis_integral :
    ∃ (s : Finset L) (b : Basis s K L), ∀ x, IsIntegral A (b x) := by
  letI := Classical.decEq L
  letI : IsNoetherian K L := IsNoetherian.iff_fg.2 inferInstance
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  have hy' : algebraMap A L y ≠ 0 := by
    refine mt ((injective_iff_map_eq_zero (algebraMap A L)).mp ?_ _) hy
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine ⟨s', bs'.map {Algebra.lmul _ _ (algebraMap A L y) with
    toFun := fun x => algebraMap A L y * x
    invFun := fun x => (algebraMap A L y)⁻¹ * x
    left_inv := ?_
    right_inv := ?_}, ?_⟩
  · intro x; simp only [inv_mul_cancel_left₀ hy']
  · intro x; simp only [mul_inv_cancel_left₀ hy']
  · rintro ⟨x', hx'⟩
    simp only [Algebra.smul_def, Finset.mem_image, exists_prop, Finset.mem_univ,
      true_and] at his'
    simp only [Basis.map_apply, LinearEquiv.coe_mk]
    exact his' _ ⟨_, rfl⟩
variable [Algebra.IsSeparable K L]
theorem IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherian A C := by
  haveI := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  letI := isNoetherian_span_of_finite A (Set.finite_range b')
  let f : C →ₗ[A] Submodule.span A (Set.range b') :=
    (Submodule.inclusion (IsIntegralClosure.range_le_span_dualBasis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).rangeRestrict
  refine isNoetherian_of_ker_bot f ?_
  rw [LinearMap.ker_comp, Submodule.ker_inclusion, Submodule.comap_bot, LinearMap.ker_codRestrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebraMap_injective C A L)
theorem IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing C :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)
theorem IsIntegralClosure.finite [IsIntegrallyClosed A] [IsNoetherianRing A] :
    Module.Finite A C := by
  haveI := IsIntegralClosure.isNoetherian A K L C
  exact Module.IsNoetherian.finite A C
theorem IsIntegralClosure.module_free [NoZeroSMulDivisors A L] [IsPrincipalIdealRing A] :
    Module.Free A C :=
  haveI : NoZeroSMulDivisors A C := IsIntegralClosure.noZeroSMulDivisors A L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  inferInstance
theorem IsIntegralClosure.rank [IsPrincipalIdealRing A] [NoZeroSMulDivisors A L] :
    Module.finrank A C = Module.finrank K L := by
  haveI : Module.Free A C := IsIntegralClosure.module_free A K L C
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Module.Free.chooseBasis A C)
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]
variable {A K}
theorem integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)
variable (A K) [IsDomain C]
theorem IsIntegralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.isIntegralClosure A L C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }
theorem integralClosure.isDedekindDomain [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
instance integralClosure.isDedekindDomain_fractionRing [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L
end IsIntegralClosure