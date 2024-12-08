import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
noncomputable section
open Module
namespace WittVector
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [CommRing k]
scoped[Isocrystal] notation "K(" p ", " k ")" => FractionRing (WittVector p k)
open Isocrystal
section PerfectRing
variable [IsDomain k] [CharP k p] [PerfectRing k p]
def FractionRing.frobenius : K(p, k) ≃+* K(p, k) :=
  IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)
def FractionRing.frobeniusRingHom : K(p, k) →+* K(p, k) :=
  FractionRing.frobenius p k
scoped[Isocrystal] notation "φ(" p ", " k ")" => WittVector.FractionRing.frobeniusRingHom p k
instance inv_pair₁ : RingHomInvPair φ(p, k) (FractionRing.frobenius p k).symm :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k)
instance inv_pair₂ : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p, k) →+* K(p, k))
    (FractionRing.frobenius p k) :=
  RingHomInvPair.of_ringEquiv (FractionRing.frobenius p k).symm
scoped[Isocrystal]
  notation:50 M " →ᶠˡ[" p ", " k "] " M₂ =>
    LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂
scoped[Isocrystal]
  notation:50 M " ≃ᶠˡ[" p ", " k "] " M₂ =>
    LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂
class Isocrystal (V : Type*) [AddCommGroup V] extends Module K(p, k) V where
  frob : V ≃ᶠˡ[p, k] V
open WittVector
variable (V : Type*) [AddCommGroup V] [Isocrystal p k V]
variable (V₂ : Type*) [AddCommGroup V₂] [Isocrystal p k V₂]
variable {V}
def Isocrystal.frobenius : V ≃ᶠˡ[p, k] V :=
  Isocrystal.frob (p := p) (k := k) (V := V)
variable (V)
scoped[Isocrystal] notation "Φ(" p ", " k ")" => WittVector.Isocrystal.frobenius p k
structure IsocrystalHom extends V →ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearMap x) = toLinearMap (Φ(p, k) x)
structure IsocrystalEquiv extends V ≃ₗ[K(p, k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p, k) (toLinearEquiv x) = toLinearEquiv (Φ(p, k) x)
scoped[Isocrystal] notation:50 M " →ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalHom p k M M₂
scoped[Isocrystal] notation:50 M " ≃ᶠⁱ[" p ", " k "] " M₂ => WittVector.IsocrystalEquiv p k M M₂
end PerfectRing
open scoped Isocrystal
@[nolint unusedArguments]
def StandardOneDimIsocrystal (_m : ℤ) : Type _ :=
  K(p, k)
section Deriving
instance {m : ℤ} : AddCommGroup (StandardOneDimIsocrystal p k m) :=
  inferInstanceAs (AddCommGroup K(p, k))
instance {m : ℤ} : Module K(p, k) (StandardOneDimIsocrystal p k m) :=
  inferInstanceAs (Module K(p, k) K(p, k))
end Deriving
section PerfectRing
variable [IsDomain k] [CharP k p] [PerfectRing k p]
instance (m : ℤ) : Isocrystal p k (StandardOneDimIsocrystal p k m) where
  frob :=
    (FractionRing.frobenius p k).toSemilinearEquiv.trans
      (LinearEquiv.smulOfNeZero _ _ _ (zpow_ne_zero m (WittVector.FractionRing.p_nonzero p k)))
@[simp]
theorem StandardOneDimIsocrystal.frobenius_apply (m : ℤ) (x : StandardOneDimIsocrystal p k m) :
    Φ(p, k) x = (p : K(p, k)) ^ m • φ(p, k) x := rfl
end PerfectRing
theorem isocrystal_classification (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (V : Type*)
    [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1) :
    ∃ m : ℤ, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0
  have : Φ(p, k) x ≠ 0 := by simpa only [map_zero] using Φ(p, k).injective.ne hx
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p, k), a ≠ 0 ∧ Φ(p, k) x = a • x := by
    rw [finrank_eq_one_iff_of_nonzero' x hx] at h_dim
    obtain ⟨a, ha⟩ := h_dim (Φ(p, k) x)
    refine ⟨a, ?_, ha.symm⟩
    intro ha'
    apply this
    simp only [← ha, ha', zero_smul]
  obtain ⟨b, hb, m, hmb⟩ := WittVector.exists_frobenius_solution_fractionRing p ha
  replace hmb : φ(p, k) b * a = (p : K(p, k)) ^ m * b := by convert hmb
  use m
  let F₀ : StandardOneDimIsocrystal p k m →ₗ[K(p, k)] V := LinearMap.toSpanSingleton K(p, k) V x
  let F : StandardOneDimIsocrystal p k m ≃ₗ[K(p, k)] V := by
    refine LinearEquiv.ofBijective F₀ ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_toSpanSingleton K(p, k) V hx
    · rw [← LinearMap.range_eq_top]
      rw [← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim]
      rw [LinearMap.span_singleton_eq_range]
  refine ⟨⟨(LinearEquiv.smulOfNeZero K(p, k) _ _ hb).trans F, fun c ↦ ?_⟩⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
    LinearEquiv.smulOfNeZero_apply, Units.smul_mk0, Units.smul_mk0, LinearEquiv.map_smul,
    LinearEquiv.map_smul]
  rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
  erw [LinearMap.toSpanSingleton_apply K(p, k) V x c, LinearMap.toSpanSingleton_apply K(p, k) V x]
  simp only [hax, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
    LinearEquiv.map_smulₛₗ, StandardOneDimIsocrystal.frobenius_apply, Algebra.id.smul_eq_mul]
  simp only [← mul_smul]
  congr 1
  linear_combination φ(p, k) c * hmb
end WittVector