import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
open scoped Polynomial
open Fintype
namespace LittleWedderburn
variable (D : Type*) [DivisionRing D]
private def InductionHyp : Prop :=
  ∀ {R : Subring D}, R < ⊤ → ∀ ⦃x y⦄, x ∈ R → y ∈ R → x * y = y * x
namespace InductionHyp
open Module Polynomial
variable {D}
private def field (hD : InductionHyp D) {R : Subring D} (hR : R < ⊤)
  [Fintype D] [DecidableEq D] [DecidablePred (· ∈ R)] :
    Field R :=
  { show DivisionRing R from Fintype.divisionRingOfIsDomain R with
    mul_comm := fun x y ↦ Subtype.ext <| hD hR x.2 y.2 }
private theorem center_eq_top [Finite D] (hD : InductionHyp D) : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  set Z := Subring.center D
  by_contra! hZ
  letI : Field Z := hD.field hZ.lt_top
  set q := card Z with card_Z
  have hq : 1 < q := by rw [card_Z]; exact one_lt_card
  let n := finrank Z D
  have card_D : card D = q ^ n := card_eq_pow_finrank
  have h1qn : 1 ≤ q ^ n := by rw [← card_D]; exact card_pos
  have key := Group.card_center_add_sum_card_noncenter_eq_card (Dˣ)
  rw [card_congr (show _ ≃* Zˣ from Subgroup.centerUnitsEquivUnitsCenter D).toEquiv,
      card_units, ← card_Z, card_units, card_D] at key
  let Φₙ := cyclotomic n ℤ
  apply_fun (Nat.cast : ℕ → ℤ) at key
  rw [Nat.cast_add, Nat.cast_sub h1qn, Nat.cast_sub hq.le, Nat.cast_one, Nat.cast_pow] at key
  suffices Φₙ.eval ↑q ∣ ↑(∑ x ∈ (ConjClasses.noncenter Dˣ).toFinset, x.carrier.toFinset.card) by
    have contra : Φₙ.eval _ ∣ _ := eval_dvd (cyclotomic.dvd_X_pow_sub_one n ℤ) (x := (q : ℤ))
    rw [eval_sub, eval_pow, eval_X, eval_one, ← key, Int.dvd_add_left this] at contra
    refine (Nat.le_of_dvd ?_ ?_).not_lt (sub_one_lt_natAbs_cyclotomic_eval (n := n) ?_ hq.ne')
    · exact tsub_pos_of_lt hq
    · convert Int.natAbs_dvd_natAbs.mpr contra
      clear_value q
      simp only [eq_comm, Int.natAbs_eq_iff, Nat.cast_sub hq.le, Nat.cast_one, neg_sub, true_or]
    · by_contra! h
      obtain ⟨x, hx⟩ := finrank_le_one_iff.mp h
      refine not_le_of_lt hZ.lt_top (fun y _ ↦ Subring.mem_center_iff.mpr fun z ↦ ?_)
      obtain ⟨r, rfl⟩ := hx y
      obtain ⟨s, rfl⟩ := hx z
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm]
  rw [Nat.cast_sum]
  apply Finset.dvd_sum
  rintro ⟨x⟩ hx
  simp (config := {zeta := false}) only [ConjClasses.quot_mk_eq_mk, Set.mem_toFinset] at hx ⊢
  set Zx := Subring.centralizer ({↑x} : Set D)
  rw [Set.toFinset_card, ConjClasses.card_carrier, ← card_congr
        (show Zxˣ ≃* _ from unitsCentralizerEquiv _ x).toEquiv, card_units, card_D]
  have hZx : Zx ≠ ⊤ := by
    by_contra! hZx
    refine (ConjClasses.mk_bijOn (Dˣ)).mapsTo (Set.subset_center_units ?_) hx
    exact Subring.centralizer_eq_top_iff_subset.mp hZx <| Set.mem_singleton _
  letI : Field Zx := hD.field hZx.lt_top
  letI : Algebra Z Zx := (Subring.inclusion <| Subring.center_le_centralizer {(x : D)}).toAlgebra
  let d := finrank Z Zx
  have card_Zx : card Zx = q ^ d := card_eq_pow_finrank
  have h1qd : 1 ≤ q ^ d := by rw [← card_Zx]; exact card_pos
  haveI : IsScalarTower Z Zx D := ⟨fun x y z ↦ mul_assoc _ _ _⟩
  rw [card_units, card_Zx, Int.natCast_div, Nat.cast_sub h1qd, Nat.cast_sub h1qn, Nat.cast_one,
      Nat.cast_pow, Nat.cast_pow]
  apply Int.dvd_div_of_mul_dvd
  have aux : ∀ {k : ℕ}, ((X : ℤ[X]) ^ k - 1).eval ↑q = (q : ℤ) ^ k - 1 := by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_self_iff_true, forall_const]
  rw [← aux, ← aux, ← eval_mul]
  refine (evalRingHom ↑q).map_dvd (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ ?_)
  refine Nat.mem_properDivisors.mpr ⟨⟨_, (finrank_mul_finrank Z Zx D).symm⟩, ?_⟩
  rw [← Nat.pow_lt_pow_iff_right hq, ← card_D, ← card_Zx]
  obtain ⟨b, -, hb⟩ := SetLike.exists_of_lt hZx.lt_top
  refine card_lt_of_injective_of_not_mem _ Subtype.val_injective (?_ : b ∉ _)
  rintro ⟨b, rfl⟩
  exact hb b.2
end InductionHyp
private theorem center_eq_top [Finite D] : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  induction' hn : Fintype.card D using Nat.strong_induction_on with n IH generalizing D
  apply InductionHyp.center_eq_top
  intro R hR x y hx hy
  suffices (⟨y, hy⟩ : R) ∈ Subring.center R by
    rw [Subring.mem_center_iff] at this
    simpa using this ⟨x, hx⟩
  let R_dr : DivisionRing R := Fintype.divisionRingOfIsDomain R
  rw [IH (Fintype.card R) _ R inferInstance rfl]
  · trivial
  rw [← hn, ← Subring.card_top D]
  convert Set.card_lt_card hR
end LittleWedderburn
open LittleWedderburn
instance (priority := 100) littleWedderburn (D : Type*) [DivisionRing D] [Finite D] : Field D :=
  { ‹DivisionRing D› with
    mul_comm := fun x y ↦ by simp [Subring.mem_center_iff.mp ?_ x, center_eq_top D] }
alias Finite.divisionRing_to_field := littleWedderburn
theorem Finite.isDomain_to_isField (D : Type*) [Finite D] [Ring D] [IsDomain D] : IsField D := by
  classical
  cases nonempty_fintype D
  let _ := Fintype.divisionRingOfIsDomain D
  let _ := littleWedderburn D
  exact Field.toIsField D