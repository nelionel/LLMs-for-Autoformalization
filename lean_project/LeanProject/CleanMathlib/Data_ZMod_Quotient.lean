import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.ZMod
open QuotientAddGroup Set ZMod
variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]
namespace Int
def quotientZMultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast
def quotientZMultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)
def quotientSpanNatEquivZMod : ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n :=
  (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans <|
    RingHom.quotientKerEquivOfRightInverse <|
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast
def quotientSpanEquivZMod (a : ℤ) : ℤ ⧸ Ideal.span ({a} : Set ℤ) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
@[simp]
lemma index_zmultiples (a : ℤ) : (AddSubgroup.zmultiples a).index = a.natAbs := by
  rw [AddSubgroup.index, Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv, Nat.card_zmod]
end Int
noncomputable section ChineseRemainder
open Ideal
def ZMod.prodEquivPi {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  have : Pairwise fun i j => IsCoprime (span {(a i : ℤ)}) (span {(a j : ℤ)}) :=
    fun _i _j h ↦ (isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R := ℤ))
  Int.quotientSpanNatEquivZMod _ |>.symm.trans <|
  quotEquivOfEq (iInf_span_singleton_natCast (R := ℤ) coprime) |>.symm.trans <|
  quotientInfRingEquivPiQuotient _ this |>.trans <|
  RingEquiv.piCongrRight fun i ↦ Int.quotientSpanNatEquivZMod (a i)
end ChineseRemainder
namespace AddAction
open AddSubgroup AddMonoidHom AddEquiv Function
variable {α β : Type*} [AddGroup α] (a : α) [AddAction α β] (b : β)
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le, mem_comap, mem_stabilizer_iff, zmultiplesHom_apply, natCast_zsmul]
              simp_rw [← vadd_iterate]
              exact isPeriodicPt_minimalPeriod (a +ᵥ ·) b))
          ⟨by
            rw [← ker_eq_bot_iff, eq_bot_iff]
            refine fun q => induction_on q fun n hn => ?_
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimalPeriod_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZMultiplesNatEquivZMod (minimalPeriod (a +ᵥ ·) b))
theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +ᵥ ·) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (cast n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl
end AddAction
namespace MulAction
open AddAction Subgroup AddSubgroup Function
variable {α β : Type*} [Group α] (a : α) [MulAction α β] (b : β)
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod (a • ·) b)) :=
  letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f
theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast n : ℤ) :=
  rfl
noncomputable def orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv
noncomputable def _root_.AddAction.orbitZMultiplesEquiv {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) :
    AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv
attribute [to_additive existing] orbitZPowersEquiv
@[to_additive]
theorem orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl
@[deprecated (since := "2024-02-21")]
alias _root_.AddAction.orbit_zmultiples_equiv_symm_apply := orbitZMultiplesEquiv_symm_apply
theorem orbitZPowersEquiv_symm_apply' (k : ℤ) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ := by
  rw [orbitZPowersEquiv_symm_apply, ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)
theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply' {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZMultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply, ZMod.coe_intCast]
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a b k)
attribute [to_additive existing]
  orbitZPowersEquiv_symm_apply'
@[to_additive]
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b), @ZMod.card _ (_)]
@[to_additive]
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod (a • ·) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    haveI : Nonempty (orbit (zpowers a) b) := (orbit_nonempty b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩
end MulAction
section Group
open Subgroup
variable {α : Type*} [Group α] (a : α)
@[to_additive (attr := simp) "See also `Fintype.card_zmultiples`."]
theorem Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this
variable {a}
@[to_additive (attr := simp)]
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, Subgroup.coe_nonempty, true_and]
@[to_additive (attr := simp)]
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not
@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers
end Group