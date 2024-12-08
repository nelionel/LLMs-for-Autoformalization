import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Cardinal
import Mathlib.SetTheory.Cardinal.Continuum
open Nat Set
open Cardinal
noncomputable section
namespace Cardinal
variable {c : ℝ} {f g : ℕ → Bool} {n : ℕ}
def cantorFunctionAux (c : ℝ) (f : ℕ → Bool) (n : ℕ) : ℝ :=
  cond (f n) (c ^ n) 0
@[simp]
theorem cantorFunctionAux_true (h : f n = true) : cantorFunctionAux c f n = c ^ n := by
  simp [cantorFunctionAux, h]
@[simp]
theorem cantorFunctionAux_false (h : f n = false) : cantorFunctionAux c f n = 0 := by
  simp [cantorFunctionAux, h]
theorem cantorFunctionAux_nonneg (h : 0 ≤ c) : 0 ≤ cantorFunctionAux c f n := by
  cases h' : f n
  · simp [h']
  · simpa [h'] using pow_nonneg h _
theorem cantorFunctionAux_eq (h : f n = g n) :
    cantorFunctionAux c f n = cantorFunctionAux c g n := by simp [cantorFunctionAux, h]
theorem cantorFunctionAux_zero (f : ℕ → Bool) : cantorFunctionAux c f 0 = cond (f 0) 1 0 := by
  cases h : f 0 <;> simp [h]
theorem cantorFunctionAux_succ (f : ℕ → Bool) :
    (fun n => cantorFunctionAux c f (n + 1)) = fun n =>
      c * cantorFunctionAux c (fun n => f (n + 1)) n := by
  ext n
  cases h : f (n + 1) <;> simp [h, _root_.pow_succ']
theorem summable_cantor_function (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    Summable (cantorFunctionAux c f) := by
  apply (summable_geometric_of_lt_one h1 h2).summable_of_eq_zero_or_self
  intro n; cases h : f n <;> simp [h]
def cantorFunction (c : ℝ) (f : ℕ → Bool) : ℝ :=
  ∑' n, cantorFunctionAux c f n
theorem cantorFunction_le (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ n, f n → g n) :
    cantorFunction c f ≤ cantorFunction c g := by
  apply tsum_le_tsum _ (summable_cantor_function f h1 h2) (summable_cantor_function g h1 h2)
  intro n; cases h : f n
  · simp [h, cantorFunctionAux_nonneg h1]
  replace h3 : g n = true := h3 n h; simp [h, h3]
theorem cantorFunction_succ (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    cantorFunction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1) := by
  rw [cantorFunction, tsum_eq_zero_add (summable_cantor_function f h1 h2)]
  rw [cantorFunctionAux_succ, tsum_mul_left, cantorFunctionAux, _root_.pow_zero]
  rfl
theorem increasing_cantorFunction (h1 : 0 < c) (h2 : c < 1 / 2) {n : ℕ} {f g : ℕ → Bool}
    (hn : ∀ k < n, f k = g k) (fn : f n = false) (gn : g n = true) :
    cantorFunction c f < cantorFunction c g := by
  have h3 : c < 1 := by
    apply h2.trans
    norm_num
  induction' n with n ih generalizing f g
  · let f_max : ℕ → Bool := fun n => Nat.rec false (fun _ _ => true) n
    have hf_max : ∀ n, f n → f_max n := by
      intro n hn
      cases n
      · rw [fn] at hn
        contradiction
      apply rfl
    let g_min : ℕ → Bool := fun n => Nat.rec true (fun _ _ => false) n
    have hg_min : ∀ n, g_min n → g n := by
      intro n hn
      cases n
      · rw [gn]
      simp at hn
    apply (cantorFunction_le (le_of_lt h1) h3 hf_max).trans_lt
    refine lt_of_lt_of_le ?_ (cantorFunction_le (le_of_lt h1) h3 hg_min)
    have : c / (1 - c) < 1 := by
      rw [div_lt_one, lt_sub_iff_add_lt]
      · convert _root_.add_lt_add h2 h2
        norm_num
      rwa [sub_pos]
    convert this
    · rw [cantorFunction_succ _ (le_of_lt h1) h3, div_eq_mul_inv, ←
        tsum_geometric_of_lt_one (le_of_lt h1) h3]
      apply zero_add
    · refine (tsum_eq_single 0 ?_).trans ?_
      · intro n hn
        cases n
        · contradiction
        rfl
      · exact cantorFunctionAux_zero _
  rw [cantorFunction_succ f (le_of_lt h1) h3, cantorFunction_succ g (le_of_lt h1) h3]
  rw [hn 0 <| zero_lt_succ n]
  apply add_lt_add_left
  rw [mul_lt_mul_left h1]
  exact ih (fun k hk => hn _ <| Nat.succ_lt_succ hk) fn gn
theorem cantorFunction_injective (h1 : 0 < c) (h2 : c < 1 / 2) :
    Function.Injective (cantorFunction c) := by
  intro f g hfg
  classical
    by_contra h
    revert hfg
    have : ∃ n, f n ≠ g n := by
      rw [← not_forall]
      intro h'
      apply h
      ext
      apply h'
    let n := Nat.find this
    have hn : ∀ k : ℕ, k < n → f k = g k := by
      intro k hk
      apply of_not_not
      exact Nat.find_min this hk
    cases fn : f n
    · apply _root_.ne_of_lt
      refine increasing_cantorFunction h1 h2 hn fn ?_
      apply Bool.eq_true_of_not_eq_false
      rw [← fn]
      apply Ne.symm
      exact Nat.find_spec this
    · apply _root_.ne_of_gt
      refine increasing_cantorFunction h1 h2 (fun k hk => (hn k hk).symm) ?_ fn
      apply Bool.eq_false_of_not_eq_true
      rw [← fn]
      apply Ne.symm
      exact Nat.find_spec this
theorem mk_real : #ℝ = 𝔠 := by
  apply le_antisymm
  · rw [Real.equivCauchy.cardinal_eq]
    apply mk_quotient_le.trans
    apply (mk_subtype_le _).trans_eq
    rw [← power_def, mk_nat, mkRat, aleph0_power_aleph0]
  · convert mk_le_of_injective (cantorFunction_injective _ _)
    · rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
    · exact 1 / 3
    · norm_num
    · norm_num
theorem mk_univ_real : #(Set.univ : Set ℝ) = 𝔠 := by rw [mk_univ, mk_real]
instance : Uncountable ℝ := by
  rw [← aleph0_lt_mk_iff, mk_real]
  exact aleph0_lt_continuum
theorem not_countable_real : ¬(Set.univ : Set ℝ).Countable :=
  not_countable_univ
theorem mk_Ioi_real (a : ℝ) : #(Ioi a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  rw [← not_lt]
  intro h
  refine _root_.ne_of_lt ?_ mk_univ_real
  have hu : Iio a ∪ {a} ∪ Ioi a = Set.univ := by
    convert @Iic_union_Ioi ℝ _ _
    exact Iio_union_right
  rw [← hu]
  refine lt_of_le_of_lt (mk_union_le _ _) ?_
  refine lt_of_le_of_lt (add_le_add_right (mk_union_le _ _) _) ?_
  have h2 : (fun x => a + a - x) '' Ioi a = Iio a := by
    convert @image_const_sub_Ioi ℝ _ _ _
    simp
  rw [← h2]
  refine add_lt_of_lt (cantor _).le ?_ h
  refine add_lt_of_lt (cantor _).le (mk_image_le.trans_lt h) ?_
  rw [mk_singleton]
  exact one_lt_aleph0.trans (cantor _)
theorem mk_Ici_real (a : ℝ) : #(Ici a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)
theorem mk_Iio_real (a : ℝ) : #(Iio a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h2 : (fun x => a + a - x) '' Iio a = Ioi a := by
    simp only [image_const_sub_Iio, add_sub_cancel_right]
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le
theorem mk_Iic_real (a : ℝ) : #(Iic a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)
theorem mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h1 : #((fun x => x - a) '' Ioo a b) ≤ #(Ioo a b) := mk_image_le
  refine le_trans ?_ h1
  rw [image_sub_const_Ioo, sub_self]
  replace h := sub_pos_of_lt h
  have h2 : #(Inv.inv '' Ioo 0 (b - a)) ≤ #(Ioo 0 (b - a)) := mk_image_le
  refine le_trans ?_ h2
  rw [image_inv_eq_inv, inv_Ioo_0_left h, mk_Ioi_real]
theorem mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)
theorem mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)
theorem mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)
end Cardinal