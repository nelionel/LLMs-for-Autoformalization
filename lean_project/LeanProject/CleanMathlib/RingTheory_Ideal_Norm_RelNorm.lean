import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Localization.NormTrace
open scoped nonZeroDivisors
section SpanNorm
namespace Ideal
open Submodule
variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
def spanNorm (I : Ideal S) : Ideal R :=
  Ideal.span (Algebra.norm R '' (I : Set S))
@[simp]
theorem spanNorm_bot [Nontrivial S] [Module.Free R S] [Module.Finite R S] :
    spanNorm R (⊥ : Ideal S) = ⊥ := span_eq_bot.mpr fun x hx => by simpa using hx
variable {R}
@[simp]
theorem spanNorm_eq_bot_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    {I : Ideal S} : spanNorm R I = ⊥ ↔ I = ⊥ := by
  simp only [spanNorm, Ideal.span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂,
    Algebra.norm_eq_zero_iff_of_basis (Module.Free.chooseBasis R S), @eq_bot_iff _ _ _ I,
    SetLike.le_def]
  rfl
variable (R)
theorem norm_mem_spanNorm {I : Ideal S} (x : S) (hx : x ∈ I) : Algebra.norm R x ∈ I.spanNorm R :=
  subset_span (Set.mem_image_of_mem _ hx)
@[simp]
theorem spanNorm_singleton {r : S} : spanNorm R (span ({r} : Set S)) = span {Algebra.norm R r} :=
  le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          exact map_dvd _ (mem_span_singleton.mp hx')))
    ((span_singleton_le_iff_mem _).mpr (norm_mem_spanNorm _ _ (mem_span_singleton_self _)))
@[simp]
theorem spanNorm_top : spanNorm R (⊤ : Ideal S) = ⊤ := by
  rw [← Ideal.span_singleton_one, spanNorm_singleton]
  simp
theorem map_spanNorm (I : Ideal S) {T : Type*} [CommRing T] (f : R →+* T) :
    map f (spanNorm R I) = span (f ∘ Algebra.norm R '' (I : Set S)) := by
  rw [spanNorm, map_span, Set.image_image]
  rfl
@[mono]
theorem spanNorm_mono {I J : Ideal S} (h : I ≤ J) : spanNorm R I ≤ spanNorm R J :=
  Ideal.span_mono (Set.monotone_image h)
theorem spanNorm_localization (I : Ideal S) [Module.Finite R S] [Module.Free R S] (M : Submonoid R)
    {Rₘ : Type*} (Sₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
    [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] :
    spanNorm Rₘ (I.map (algebraMap S Sₘ)) = (spanNorm R I).map (algebraMap R Rₘ) := by
  cases subsingleton_or_nontrivial R
  · haveI := IsLocalization.unique R Rₘ M
    simp [eq_iff_true_of_subsingleton]
  let b := Module.Free.chooseBasis R S
  rw [map_spanNorm]
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · rintro a' ha'
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    refine ⟨⟨Algebra.norm R a, norm_mem_spanNorm _ _ ha⟩,
      ⟨s ^ Fintype.card (Module.Free.ChooseBasisIndex R S), pow_mem hs _⟩, ?_⟩
    simp only [Submodule.coe_mk, Subtype.coe_mk, map_pow] at has ⊢
    apply_fun Algebra.norm Rₘ at has
    rwa [_root_.map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ,
      Algebra.norm_algebraMap_of_basis (b.localizationLocalization Rₘ M Sₘ),
      Algebra.norm_localization R M a] at has
  · intro a ha
    rw [Set.mem_preimage, Function.comp_apply, ← Algebra.norm_localization (Sₘ := Sₘ) R M a]
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))
theorem spanNorm_mul_spanNorm_le (I J : Ideal S) :
    spanNorm R I * spanNorm R J ≤ spanNorm R (I * J) := by
  rw [spanNorm, spanNorm, spanNorm, Ideal.span_mul_span', ← Set.image_mul]
  refine Ideal.span_mono (Set.monotone_image ?_)
  rintro _ ⟨x, hxI, y, hyJ, rfl⟩
  exact Ideal.mul_mem_mul hxI hyJ
theorem spanNorm_mul_of_bot_or_top [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    (eq_bot_or_top : ∀ I : Ideal R, I = ⊥ ∨ I = ⊤) (I J : Ideal S) :
    spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
  cases' eq_bot_or_top (spanNorm R I) with hI hI
  · rw [hI, spanNorm_eq_bot_iff.mp hI, bot_mul, spanNorm_bot]
    exact bot_le
  rw [hI, Ideal.top_mul]
  cases' eq_bot_or_top (spanNorm R J) with hJ hJ
  · rw [hJ, spanNorm_eq_bot_iff.mp hJ, mul_bot, spanNorm_bot]
  rw [hJ]
  exact le_top
@[simp]
theorem spanNorm_mul_of_field {K : Type*} [Field K] [Algebra K S] [IsDomain S] [Module.Finite K S]
    (I J : Ideal S) : spanNorm K (I * J) = spanNorm K I * spanNorm K J :=
  spanNorm_mul_of_bot_or_top K eq_bot_or_top I J
variable [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
variable [Module.Finite R S] [Module.Free R S]
theorem spanNorm_mul (I J : Ideal S) : spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  nontriviality R
  cases subsingleton_or_nontrivial S
  · have : ∀ I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    simp [this I, this J, this (I * J)]
  refine eq_of_localization_maximal ?_
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [spanNorm_mul_of_bot_or_top]
    intro I
    refine or_iff_not_imp_right.mpr fun hI => ?_
    exact (hP.eq_of_le hI bot_le).symm
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  letI : Algebra (Localization.AtPrime P) (Localization P') := localizationAlgebra P.primeCompl S
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization P') :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization P') := IsLocalization.isDomain_localization h
  haveI : IsDedekindDomain (Localization P') := IsLocalization.isDedekindDomain S h _
  letI := Classical.decEq (Ideal (Localization P'))
  haveI : IsPrincipalIdealRing (Localization P') :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P hP0
  rw [Ideal.map_mul, ← spanNorm_localization R I P.primeCompl (Localization P'),
    ← spanNorm_localization R J P.primeCompl (Localization P'),
    ← spanNorm_localization R (I * J) P.primeCompl (Localization P'), Ideal.map_mul,
    ← (I.map _).span_singleton_generator, ← (J.map _).span_singleton_generator,
    span_singleton_mul_span_singleton, spanNorm_singleton, spanNorm_singleton,
    spanNorm_singleton, span_singleton_mul_span_singleton, _root_.map_mul]
def relNorm : Ideal S →*₀ Ideal R where
  toFun := spanNorm R
  map_zero' := spanNorm_bot R
  map_one' := by dsimp only; rw [one_eq_top, spanNorm_top R, one_eq_top]
  map_mul' := spanNorm_mul R
theorem relNorm_apply (I : Ideal S) : relNorm R I = span (Algebra.norm R '' (I : Set S) : Set R) :=
  rfl
@[simp]
theorem spanNorm_eq (I : Ideal S) : spanNorm R I = relNorm R I := rfl
@[simp]
theorem relNorm_bot : relNorm R (⊥ : Ideal S) = ⊥ := by
  simpa only [zero_eq_bot] using map_zero (relNorm R : Ideal S →*₀ _)
@[simp]
theorem relNorm_top : relNorm R (⊤ : Ideal S) = ⊤ := by
  simpa only [one_eq_top] using map_one (relNorm R : Ideal S →*₀ _)
variable {R}
@[simp]
theorem relNorm_eq_bot_iff {I : Ideal S} : relNorm R I = ⊥ ↔ I = ⊥ :=
  spanNorm_eq_bot_iff
variable (R)
theorem norm_mem_relNorm (I : Ideal S) {x : S} (hx : x ∈ I) : Algebra.norm R x ∈ relNorm R I :=
  norm_mem_spanNorm R x hx
@[simp]
theorem relNorm_singleton (r : S) : relNorm R (span ({r} : Set S)) = span {Algebra.norm R r} :=
  spanNorm_singleton R
theorem map_relNorm (I : Ideal S) {T : Type*} [CommRing T] (f : R →+* T) :
    map f (relNorm R I) = span (f ∘ Algebra.norm R '' (I : Set S)) :=
  map_spanNorm R I f
@[mono]
theorem relNorm_mono {I J : Ideal S} (h : I ≤ J) : relNorm R I ≤ relNorm R J :=
  spanNorm_mono R h
end Ideal
end SpanNorm