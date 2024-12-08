import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Polynomial.RationalRoot
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
open scoped nonZeroDivisors Polynomial
class Ring.DimensionLEOne : Prop where
  (maximalOfPrime : ∀ {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal)
open Ideal Ring
theorem Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R]
    {p : Ideal R} (h : p.IsPrime) (hp : p ≠ ⊥) : p.IsMaximal :=
  DimensionLEOne.maximalOfPrime hp h
namespace Ring
instance DimensionLEOne.principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] :
    DimensionLEOne A where
  maximalOfPrime := fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero
theorem DimensionLEOne.isIntegralClosure (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R]
    [Algebra R A] [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A]
    [DimensionLEOne R] : DimensionLEOne B where
  maximalOfPrime := fun {p} ne_bot _ =>
    IsIntegralClosure.isMaximal_of_isMaximal_comap (R := R) A p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegralClosure.comap_ne_bot A ne_bot))
nonrec instance DimensionLEOne.integralClosure [Nontrivial R] [IsDomain A] [Algebra R A]
    [DimensionLEOne R] : DimensionLEOne (integralClosure R A) :=
  DimensionLEOne.isIntegralClosure R A (integralClosure R A)
variable {R}
theorem DimensionLEOne.not_lt_lt [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.ne ((hp₁.isMaximal (bot_le.trans_lt h01).ne').eq_of_le hp₂.ne_top h12.le)
theorem DimensionLEOne.eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime]
    [P.IsPrime] (hpP : p < P) : p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩
end Ring
class IsDedekindRing
  extends IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A) : Prop
theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩
class IsDedekindDomain
  extends IsDomain A, IsDedekindRing A : Prop
attribute [instance 90] IsDedekindDomain.toIsDomain
instance [IsDomain A] [IsDedekindRing A] : IsDedekindDomain A where
theorem isDedekindDomain_iff (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain
    [IsDomain A] [IsPrincipalIdealRing A] :
    IsDedekindDomain A :=
  { PrincipalIdealRing.isNoetherianRing, Ring.DimensionLEOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.instIsIntegrallyClosed with }