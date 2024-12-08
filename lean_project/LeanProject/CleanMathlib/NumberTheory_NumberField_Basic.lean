import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
@[stacks 09GA]
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]
open Function Module
open scoped nonZeroDivisors
theorem Int.not_isField : ¬IsField ℤ := fun h =>
  Int.not_even_one <|
    (h.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul]; exact Eq.symm
namespace NumberField
variable (K L : Type*) [Field K] [Field L]
attribute [instance] NumberField.to_charZero NumberField.to_finiteDimensional
protected theorem isAlgebraic [NumberField K] : Algebra.IsAlgebraic ℚ K :=
  Algebra.IsAlgebraic.of_finite _ _
instance [NumberField K] [NumberField L] [Algebra K L] : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L
theorem of_module_finite [NumberField K] [Algebra K L] [Module.Finite K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L
variable {K} {L} in
instance of_intermediateField [NumberField K] [NumberField L] [Algebra K L]
    (E : IntermediateField K L) : NumberField E :=
  of_module_finite K E
theorem of_tower [NumberField K] [NumberField L] [Algebra K L] (E : Type*) [Field E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L] : NumberField E :=
  letI := Module.Finite.left K E L
  of_module_finite K E
def RingOfIntegers : Type _ :=
  integralClosure ℤ K
@[inherit_doc] scoped notation "𝓞" => NumberField.RingOfIntegers
namespace RingOfIntegers
instance : CommRing (𝓞 K) :=
  inferInstanceAs (CommRing (integralClosure _ _))
instance : IsDomain (𝓞 K) :=
  inferInstanceAs (IsDomain (integralClosure _ _))
instance [NumberField K] : CharZero (𝓞 K) :=
  inferInstanceAs (CharZero (integralClosure _ _))
instance : Algebra (𝓞 K) K :=
  inferInstanceAs (Algebra (integralClosure _ _) _)
instance : NoZeroSMulDivisors (𝓞 K) K :=
  inferInstanceAs (NoZeroSMulDivisors (integralClosure _ _) _)
instance : Nontrivial (𝓞 K) :=
  inferInstanceAs (Nontrivial (integralClosure _ _))
instance {L : Type*} [Ring L] [Algebra K L] : Algebra (𝓞 K) L :=
  inferInstanceAs (Algebra (integralClosure _ _) L)
instance {L : Type*} [Ring L] [Algebra K L] : IsScalarTower (𝓞 K) K L :=
  inferInstanceAs (IsScalarTower (integralClosure _ _) K L)
variable {K}
@[coe]
abbrev val (x : 𝓞 K) : K := algebraMap _ _ x
instance : CoeHead (𝓞 K) K := ⟨val⟩
lemma coe_eq_algebraMap (x : 𝓞 K) : (x : K) = algebraMap _ _ x := rfl
@[ext] theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
  Subtype.ext h
@[norm_cast]
theorem eq_iff {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y :=
  NumberField.RingOfIntegers.ext_iff.symm
@[simp] lemma map_mk (x : K) (hx) : algebraMap (𝓞 K) K ⟨x, hx⟩ = x := rfl
lemma coe_mk {x : K} (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x := rfl
lemma mk_eq_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) = ⟨y, hy⟩ ↔ x = y := by simp
@[simp] lemma mk_one : (⟨1, one_mem _⟩ : 𝓞 K) = 1 :=
  rfl
@[simp] lemma mk_zero : (⟨0, zero_mem _⟩ : 𝓞 K) = 0 :=
  rfl
@[simp] lemma mk_add_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) + ⟨y, hy⟩ = ⟨x + y, add_mem hx hy⟩ :=
  rfl
@[simp] lemma mk_mul_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl
@[simp] lemma mk_sub_mk (x y : K) (hx hy) : (⟨x, hx⟩ : 𝓞 K) - ⟨y, hy⟩ = ⟨x - y, sub_mem hx hy⟩ :=
  rfl
@[simp] lemma neg_mk (x : K) (hx) : (-⟨x, hx⟩ : 𝓞 K) = ⟨-x, neg_mem hx⟩ :=
  rfl
def mapRingHom {K L F : Type*} [Field K] [Field L] [FunLike F K L]
    [RingHomClass F K L] (f : F) : (𝓞 K) →+* (𝓞 L) where
  toFun k := ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y:= by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]
def mapRingEquiv {K L E : Type*} [Field K] [Field L] [EquivLike E K L]
    [RingEquivClass E K L] (e : E) : (𝓞 K) ≃+* (𝓞 L) :=
  RingEquiv.ofRingHom (mapRingHom e) (mapRingHom (e : K ≃+* L).symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))
end RingOfIntegers
instance inst_ringOfIntegersAlgebra [Algebra K L] : Algebra (𝓞 K) (𝓞 L) :=
  (RingOfIntegers.mapRingHom (algebraMap K L)).toAlgebra
example : Algebra.id (𝓞 K) = inst_ringOfIntegersAlgebra K K := rfl
namespace RingOfIntegers
def mapAlgHom {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) →ₐ[𝓞 k] (𝓞 L) where
  toRingHom := mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes ((f : K →ₐ[k] L).restrictScalars (𝓞 k)) x)
def mapAlgEquiv {k K L E : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [EquivLike E K L] [AlgEquivClass E k K L] (e : E) : (𝓞 K) ≃ₐ[𝓞 k] (𝓞 L) :=
  AlgEquiv.ofAlgHom (mapAlgHom e) (mapAlgHom (e : K ≃ₐ[k] L).symm)
    (AlgHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (AlgHom.ext fun x => ext (EquivLike.left_inv e x.1))
instance inst_isScalarTower (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    IsScalarTower (𝓞 k) (𝓞 K) (𝓞 L) :=
  IsScalarTower.of_algHom (mapAlgHom (IsScalarTower.toAlgHom k K L))
variable {K}
lemma coe_injective : Function.Injective (algebraMap (𝓞 K) K) :=
  NoZeroSMulDivisors.algebraMap_injective _ _
lemma coe_eq_zero_iff {x : 𝓞 K} : algebraMap _ K x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ coe_injective
lemma coe_ne_zero_iff {x : 𝓞 K} : algebraMap _ K x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero_iff _ coe_injective
theorem isIntegral_coe (x : 𝓞 K) : IsIntegral ℤ (algebraMap _ K x) :=
  x.2
theorem isIntegral (x : 𝓞 K) : IsIntegral ℤ x := by
  obtain ⟨P, hPm, hP⟩ := x.isIntegral_coe
  refine ⟨P, hPm, ?_⟩
  rwa [IsScalarTower.algebraMap_eq (S := 𝓞 K), ← Polynomial.hom_eval₂, coe_eq_zero_iff] at hP
instance [NumberField K] : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ _
instance : IsIntegralClosure (𝓞 K) ℤ K :=
  integralClosure.isIntegralClosure _ _
instance : Algebra.IsIntegral ℤ (𝓞 K) :=
  IsIntegralClosure.isIntegral_algebra ℤ K
instance [NumberField K] : IsIntegrallyClosed (𝓞 K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension ℚ
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra R K]
    [IsIntegralClosure R ℤ K] : 𝓞 K ≃+* R :=
  (IsIntegralClosure.equiv ℤ R K _).symm.toRingEquiv
variable (K)
instance [CharZero K] : CharZero (𝓞 K) :=
  CharZero.of_module _ K
variable [NumberField K]
instance : IsNoetherian ℤ (𝓞 K) :=
  IsIntegralClosure.isNoetherian _ ℚ K _
theorem not_isField : ¬IsField (𝓞 K) := by
  have h_inj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int (algebraMap ℤ (𝓞 K))
  intro hf
  exact Int.not_isField
    (((IsIntegralClosure.isIntegral_algebra ℤ K).isField_iff_isField h_inj).mpr hf)
instance : IsDedekindDomain (𝓞 K) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ K _
instance : Free ℤ (𝓞 K) :=
  IsIntegralClosure.module_free ℤ ℚ K (𝓞 K)
instance : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) K :=
  IsIntegralClosure.isLocalization_of_isSeparable ℤ ℚ K (𝓞 K)
noncomputable def basis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ (𝓞 K) :=
  Free.chooseBasis ℤ (𝓞 K)
variable {K} {M : Type*}
def restrict (f : M → K) (h : ∀ x, IsIntegral ℤ (f x)) (x : M) : 𝓞 K :=
  ⟨f x, h x⟩
def restrict_addMonoidHom [AddZeroClass M] (f : M →+ K) (h : ∀ x, IsIntegral ℤ (f x)) :
    M →+ 𝓞 K where
  toFun := restrict f h
  map_zero' := by simp only [restrict, map_zero, mk_zero]
  map_add' x y := by simp only [restrict, map_add, mk_add_mk _]
@[to_additive existing] 
def restrict_monoidHom [MulOneClass M] (f : M →* K) (h : ∀ x, IsIntegral ℤ (f x)) : M →* 𝓞 K where
  toFun := restrict f h
  map_one' := by simp only [restrict, map_one, mk_one]
  map_mul' x y := by simp only [restrict, map_mul, mk_mul_mk _]
section extension
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
instance : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq' rfl
instance : IsIntegralClosure (𝓞 L) (𝓞 K) L :=
  IsIntegralClosure.tower_top (R := ℤ)
protected noncomputable def algEquiv (R : Type*) [CommRing R] [Algebra (𝓞 K) R] [Algebra R L]
    [IsScalarTower (𝓞 K) R L] [IsIntegralClosure R (𝓞 K) L] : 𝓞 L ≃ₐ[𝓞 K] R :=
  (IsIntegralClosure.equiv (𝓞 K) R L _).symm
instance extension_algebra_isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L
instance extension_isNoetherian [NumberField K] [NumberField L] : IsNoetherian (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)
theorem ker_algebraMap_eq_bot : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ :=
  (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr <| fun x hx => by
  have h : (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h
theorem algebraMap.injective : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (ker_algebraMap_eq_bot K L)
instance : NoZeroSMulDivisors (𝓞 K) (𝓞 L) :=
  NoZeroSMulDivisors.of_algebraMap_injective (algebraMap.injective K L)
instance : NoZeroSMulDivisors (𝓞 K) L :=
  NoZeroSMulDivisors.trans (𝓞 K) (𝓞 L) L
end extension
end RingOfIntegers
variable [NumberField K]
noncomputable def integralBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K)
@[simp]
theorem integralBasis_apply (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    integralBasis K i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) :=
  Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K) i
@[simp]
theorem integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (integralBasis K).repr (algebraMap _ _ x) i =
      (algebraMap ℤ ℚ) ((RingOfIntegers.basis K).repr x i) :=
  Basis.localizationLocalization_repr_algebraMap ℚ (nonZeroDivisors ℤ) K _ x i
theorem mem_span_integralBasis {x : K} :
    x ∈ Submodule.span ℤ (Set.range (integralBasis K)) ↔ x ∈ (algebraMap (𝓞 K) K).range := by
  rw [integralBasis, Basis.localizationLocalization_span, LinearMap.mem_range,
      IsScalarTower.coe_toAlgHom', RingHom.mem_range]
theorem RingOfIntegers.rank : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
  IsIntegralClosure.rank ℤ ℚ K (𝓞 K)
end NumberField
namespace Rat
open NumberField
instance numberField : NumberField ℚ where
  to_charZero := inferInstance
  to_finiteDimensional := by
    convert (inferInstance : FiniteDimensional ℚ ℚ)
noncomputable def ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ :=
  RingOfIntegers.equiv ℤ
end Rat
namespace AdjoinRoot
section
open scoped Polynomial
attribute [-instance] DivisionRing.toRatAlgebra
instance {f : Polynomial ℚ} [hf : Fact (Irreducible f)] : NumberField (AdjoinRoot f) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := by convert (AdjoinRoot.powerBasis hf.out.ne_zero).finite
end
end AdjoinRoot