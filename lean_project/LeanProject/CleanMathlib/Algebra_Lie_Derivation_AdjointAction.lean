import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.OfAssociative
namespace LieDerivation
section AdjointAction
variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
@[simps!]
def ad : L →ₗ⁅R⁆ LieDerivation R L L :=
  { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie, neg_lie, neg_lie, ← lie_skew x]
      abel }
variable {R L}
@[simp] lemma coe_ad_apply_eq_ad_apply (x : L) : ad R L x = LieAlgebra.ad R L x := by ext; simp
lemma ad_apply_lieDerivation (x : L) (D : LieDerivation R L L) : ad R L (D x) = - ⁅x, D⁆ := rfl
lemma lie_ad (x : L) (D : LieDerivation R L L) : ⁅ad R L x, D⁆ = ⁅x, D⁆ := by ext; simp
variable (R L) in
lemma ad_ker_eq_center : (ad R L).ker = LieAlgebra.center R L := by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center, LieHom.mem_ker, LieModule.mem_ker]
  simp [DFunLike.ext_iff]
lemma injective_ad_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    Function.Injective (ad R L) := by
  rw [← LieHom.ker_eq_bot, ad_ker_eq_center, h]
lemma lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, ad R L x⁆ = ad R L (D x) := by
  rw [ad_apply_lieDerivation, ← lie_ad, lie_skew]
variable (R L) in
lemma ad_isIdealMorphism : (ad R L).IsIdealMorphism := by
  simp_rw [LieHom.isIdealMorphism_iff, lie_der_ad_eq_ad_der]
  tauto
lemma mem_ad_idealRange_iff {D : LieDerivation R L L} :
    D ∈ (ad R L).idealRange ↔ ∃ x : L, ad R L x = D :=
  (ad R L).mem_idealRange_iff (ad_isIdealMorphism R L)
lemma maxTrivSubmodule_eq_bot_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    LieModule.maxTrivSubmodule R L (LieDerivation R L L) = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD ↦ ext fun x ↦ ?_
  have : ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker, ad_ker_eq_center, h, LieSubmodule.mem_bot] at this
  simp [this]
end AdjointAction
end LieDerivation