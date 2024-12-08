import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Basic
universe u v
noncomputable section
open scoped unitInterval
open Path ContinuousMap Set.Icc TopologicalSpace
class HSpace (X : Type u) [TopologicalSpace X] where
  hmul : C(X × X, X)
  e : X
  hmul_e_e : hmul (e, e) = e
  eHmul :
    (hmul.comp <| (const X e).prodMk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
  hmulE :
    (hmul.comp <| (ContinuousMap.id X).prodMk <| const X e).HomotopyRel (ContinuousMap.id X) {e}
scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)
open HSpaces
instance HSpace.prod (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] [HSpace X]
    [HSpace Y] : HSpace (X × Y) where
  hmul := ⟨fun p => (p.1.1 ⋀ p.2.1, p.1.2 ⋀ p.2.2), by
    exact ((map_continuous HSpace.hmul).comp ((continuous_fst.comp continuous_fst).prod_mk
        (continuous_fst.comp continuous_snd))).prod_mk ((map_continuous HSpace.hmul).comp
        ((continuous_snd.comp continuous_fst).prod_mk (continuous_snd.comp continuous_snd)))
  ⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk.inj_iff]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul := by
    let G : I × X × Y → X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G :=
      (Continuous.comp HSpace.eHmul.1.1.2
          (continuous_fst.prod_mk (continuous_fst.comp continuous_snd))).prod_mk
        (Continuous.comp HSpace.eHmul.1.1.2
          (continuous_fst.prod_mk (continuous_snd.comp continuous_snd)))
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.2 x) (HSpace.eHmul.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.3 x) (HSpace.eHmul.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk.inj_iff.mp h
      exact Prod.ext (HSpace.eHmul.2 t x h.1) (HSpace.eHmul.2 t y h.2)
  hmulE := by
    let G : I × X × Y → X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G :=
      (Continuous.comp HSpace.hmulE.1.1.2
            (continuous_fst.prod_mk (continuous_fst.comp continuous_snd))).prod_mk
        (Continuous.comp HSpace.hmulE.1.1.2
          (continuous_fst.prod_mk (continuous_snd.comp continuous_snd)))
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.2 x) (HSpace.hmulE.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.3 x) (HSpace.hmulE.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk.inj_iff.mp h
      exact Prod.ext (HSpace.hmulE.2 t x h.1) (HSpace.hmulE.2 t y h.2)
namespace TopologicalGroup
@[to_additive
      "The definition `toHSpace` is not an instance because it comes together with a
      multiplicative version which would lead to a diamond since a topological field would inherit
      two `HSpace` structures, one from the `MulOneClass` and one from the `AddZeroClass`.
      In the case of an additive group, we make `TopologicalAddGroup.hSpace` an instance."]
def toHSpace (M : Type u) [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] : HSpace M where
  hmul := ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)
@[to_additive]
instance (priority := 600) hSpace (G : Type u) [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    HSpace G :=
  toHSpace G
theorem one_eq_hSpace_e {G : Type u} [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    (1 : G) = HSpace.e :=
  rfl
example {G G' : Type u} [TopologicalSpace G] [Group G] [TopologicalGroup G] [TopologicalSpace G']
    [Group G'] [TopologicalGroup G'] : TopologicalGroup.hSpace (G × G') = HSpace.prod G G' := by
  simp only [HSpace.prod]
  rfl
end TopologicalGroup
namespace unitInterval
def qRight (p : I × I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))
theorem continuous_qRight : Continuous qRight :=
  continuous_projIcc.comp <|
    Continuous.div (by fun_prop) (by fun_prop) fun _ ↦ (add_pos zero_lt_one).ne'
theorem qRight_zero_left (θ : I) : qRight (0, θ) = 0 :=
  Set.projIcc_of_le_left _ <| by simp only [coe_zero, mul_zero, zero_div, le_refl]
theorem qRight_one_left (θ : I) : qRight (1, θ) = 1 :=
  Set.projIcc_of_right_le _ <|
    (le_div_iff₀ <| add_pos zero_lt_one).2 <| by
      dsimp only
      rw [coe_one, one_mul, mul_one, add_comm, ← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _
theorem qRight_zero_right (t : I) :
    (qRight (t, 0) : ℝ) = if (t : ℝ) ≤ 1 / 2 then (2 : ℝ) * t else 1 := by
  simp only [qRight, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]
    refine ⟨t.2.1, ?_⟩
    tauto
  · rw [(Set.projIcc_eq_right _).2]
    · linarith
    · exact zero_lt_one
theorem qRight_one_right (t : I) : qRight (t, 1) = t :=
  Eq.trans (by rw [qRight]; norm_num) <| Set.projIcc_val zero_le_one _
end unitInterval
namespace Path
open unitInterval
variable {X : Type u} [TopologicalSpace X] {x y : X}
def delayReflRight (θ : I) (γ : Path x y) : Path x y where
  toFun t := γ (qRight (t, θ))
  continuous_toFun := γ.continuous.comp (continuous_qRight.comp <| Continuous.Prod.mk_left θ)
  source' := by
    dsimp only
    rw [qRight_zero_left, γ.source]
  target' := by
    dsimp only
    rw [qRight_one_left, γ.target]
theorem continuous_delayReflRight : Continuous fun p : I × Path x y => delayReflRight p.1 p.2 :=
  continuous_uncurry_iff.mp <|
    (continuous_snd.comp continuous_fst).eval <|
      continuous_qRight.comp <| continuous_snd.prod_mk <| continuous_fst.comp continuous_fst
theorem delayReflRight_zero (γ : Path x y) : delayReflRight 0 γ = γ.trans (Path.refl y) := by
  ext t
  simp only [delayReflRight, trans_apply, refl_extend, Path.coe_mk_mk, Function.comp_apply,
    refl_apply]
  split_ifs with h; swap
  on_goal 1 => conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [qRight_zero_right]
  exacts [if_neg h, if_pos h]
theorem delayReflRight_one (γ : Path x y) : delayReflRight 1 γ = γ := by
  ext t
  exact congr_arg γ (qRight_one_right t)
def delayReflLeft (θ : I) (γ : Path x y) : Path x y :=
  (delayReflRight θ γ.symm).symm
theorem continuous_delayReflLeft : Continuous fun p : I × Path x y => delayReflLeft p.1 p.2 :=
  Path.continuous_symm.comp <|
    continuous_delayReflRight.comp <|
      continuous_fst.prod_mk <| Path.continuous_symm.comp continuous_snd
theorem delayReflLeft_zero (γ : Path x y) : delayReflLeft 0 γ = (Path.refl x).trans γ := by
  simp only [delayReflLeft, delayReflRight_zero, trans_symm, refl_symm, Path.symm_symm]
theorem delayReflLeft_one (γ : Path x y) : delayReflLeft 1 γ = γ := by
  simp only [delayReflLeft, delayReflRight_one, Path.symm_symm]
instance (x : X) : HSpace (Path x x) where
  hmul := ⟨fun ρ => ρ.1.trans ρ.2, continuous_trans⟩
  e := refl x
  hmul_e_e := refl_trans_refl
  eHmul :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x ↦ delayReflLeft p.1 p.2, continuous_delayReflLeft⟩,
          delayReflLeft_zero, delayReflLeft_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }
  hmulE :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x ↦ delayReflRight p.1 p.2, continuous_delayReflRight⟩,
          delayReflRight_zero, delayReflRight_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }
end Path