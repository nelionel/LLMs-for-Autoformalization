import Mathlib.SetTheory.Ordinal.Arithmetic
namespace Cardinal
universe u
variable {α : Type u}
variable (g : Ordinal → α)
open Cardinal Ordinal SuccOrder Function Set
theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
  exact not_le_of_lt (Order.lt_succ #α) h
end Cardinal
namespace OrdinalApprox
universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α →o α) (x : α)
open Function fixedPoints Cardinal Order OrderHom
set_option linter.unusedVariables false in
def lfpApprox (a : Ordinal.{u}) : α :=
  sSup ({ f (lfpApprox b) | (b : Ordinal) (h : b < a) } ∪ {x})
termination_by a
decreasing_by exact h
theorem lfpApprox_monotone : Monotone (lfpApprox f x) := by
  intros a b h
  rw [lfpApprox, lfpApprox]
  refine sSup_le_sSup ?h
  apply sup_le_sup_right
  simp only [exists_prop, Set.le_eq_subset, Set.setOf_subset_setOf, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intros a' h'
  use a'
  exact ⟨lt_of_lt_of_le h' h, rfl⟩
theorem le_lfpApprox {a : Ordinal} : x ≤ lfpApprox f x a := by
  rw [lfpApprox]
  apply le_sSup
  simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, true_or]
theorem lfpApprox_add_one (h : x ≤ f x) (a : Ordinal) :
    lfpApprox f x (a+1) = f (lfpApprox f x a) := by
  apply le_antisymm
  · conv => left; rw [lfpApprox]
    apply sSup_le
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, forall_eq_or_imp, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · apply le_trans h
      apply Monotone.imp f.monotone
      exact le_lfpApprox f x
    · intros a' h
      apply f.2; apply lfpApprox_monotone; exact h
  · conv => right; rw [lfpApprox]
    apply le_sSup
    simp only [Ordinal.add_one_eq_succ, lt_succ_iff, exists_prop]
    rw [Set.mem_union]
    apply Or.inl
    simp only [Set.mem_setOf_eq]
    use a
theorem lfpApprox_mono_left : Monotone (lfpApprox : (α →o α) → _) := by
  intro f g h x a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sSup_insert,
      forall_eq_or_imp, le_sup_left, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      true_and]
    intro i' h_lt
    apply le_sup_of_le_right
    apply le_sSup_of_le
    · use i'
    · apply le_trans (h _)
      simp only [OrderHom.toFun_eq_coe]
      exact g.monotone (ih i' h_lt)
theorem lfpApprox_mono_mid : Monotone (lfpApprox f) := by
  intro x₁ x₂ h a
  induction a using Ordinal.induction with
  | h i ih =>
    rw [lfpApprox, lfpApprox]
    apply sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sSup_insert,
      forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · exact le_sup_of_le_left h
    · intro i' h_i'
      apply le_sup_of_le_right
      apply le_sSup_of_le
      · use i'
      · exact f.monotone (ih i' h_i')
theorem lfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_init : x ≤ f x) (h_ab : a ≤ b)
    (h : lfpApprox f x a ∈ fixedPoints f) : lfpApprox f x b = lfpApprox f x a := by
  rw [mem_fixedPoints_iff] at h
  induction b using Ordinal.induction with | h b IH =>
  apply le_antisymm
  · conv => left; rw [lfpApprox]
    apply sSup_le
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
      forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply And.intro (le_lfpApprox f x)
    intro a' ha'b
    by_cases haa : a' < a
    · rw [← lfpApprox_add_one f x h_init]
      apply lfpApprox_monotone
      simp only [Ordinal.add_one_eq_succ, succ_le_iff]
      exact haa
    · rw [IH a' ha'b (le_of_not_lt haa), h]
  · exact lfpApprox_monotone f x h_ab
theorem exists_lfpApprox_eq_lfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ lfpApprox f x a = lfpApprox f x b := by
  have h_ninj := not_injective_limitation_set <| lfpApprox f x
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab
lemma lfpApprox_mem_fixedPoints_of_eq {a b c : Ordinal}
    (h_init : x ≤ f x) (h_ab : a < b) (h_ac : a ≤ c) (h_fab : lfpApprox f x a = lfpApprox f x b) :
    lfpApprox f x c ∈ fixedPoints f := by
  have lfpApprox_mem_fixedPoint :
      lfpApprox f x a ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, ← lfpApprox_add_one f x h_init]
    exact Monotone.eq_of_le_of_le (lfpApprox_monotone f x)
      h_fab (SuccOrder.le_succ a) (SuccOrder.succ_le_of_lt h_ab)
  rw [lfpApprox_eq_of_mem_fixedPoints f x h_init]
  · exact lfpApprox_mem_fixedPoint
  · exact h_ac
  · exact lfpApprox_mem_fixedPoint
theorem lfpApprox_ord_mem_fixedPoint (h_init : x ≤ f x) :
    lfpApprox f x (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, h_a, b, h_b, h_nab, h_fab⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl h_ab =>
    exact lfpApprox_mem_fixedPoints_of_eq f x h_init
      (h_nab.lt_of_le h_ab) (le_of_lt h_a) h_fab
  | inr h_ba =>
    exact lfpApprox_mem_fixedPoints_of_eq f x h_init
      (h_nab.symm.lt_of_le h_ba) (le_of_lt h_b) (h_fab.symm)
theorem lfpApprox_le_of_mem_fixedPoints {a : α}
    (h_a : a ∈ fixedPoints f) (h_le_init : x ≤ a) (i : Ordinal) : lfpApprox f x i ≤ a := by
  induction i using Ordinal.induction with
  | h i IH =>
    rw [lfpApprox]
    apply sSup_le
    simp only [exists_prop]
    intro y h_y
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at h_y
    cases h_y with
    | inl h_y =>
      let ⟨j, h_j_lt, h_j⟩ := h_y
      rw [← h_j, ← h_a]
      exact f.monotone' (IH j h_j_lt)
    | inr h_y =>
      rw [h_y]
      exact h_le_init
theorem lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord <| succ #α) = f.lfp := by
  apply le_antisymm
  · have h_lfp : ∃ y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f ⊥ y.2 bot_le (ord <| succ #α)
  · have h_fix : ∃ y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_ord_mem_fixedPoint f ⊥ bot_le
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop
theorem lfp_mem_range_lfpApprox : f.lfp ∈ Set.range (lfpApprox f ⊥) := by
  use ord <| succ #α
  exact lfpApprox_ord_eq_lfp f
set_option linter.unusedVariables false in
def gfpApprox (a : Ordinal.{u}) : α :=
  sInf ({ f (gfpApprox b) | (b : Ordinal) (h : b < a) } ∪ {x})
termination_by a
decreasing_by exact h
unseal gfpApprox lfpApprox
theorem gfpApprox_antitone : Antitone (gfpApprox f x) :=
  lfpApprox_monotone f.dual x
theorem gfpApprox_le {a : Ordinal} : gfpApprox f x a ≤ x :=
  le_lfpApprox f.dual x
theorem gfpApprox_add_one (h : f x ≤ x) (a : Ordinal) :
    gfpApprox f x (a+1) = f (gfpApprox f x a) :=
  lfpApprox_add_one f.dual x h a
theorem gfpApprox_mono_left : Monotone (gfpApprox : (α →o α) → _) := by
  intro f g h
  have : g.dual ≤ f.dual := h
  exact lfpApprox_mono_left this
theorem gfpApprox_mono_mid : Monotone (gfpApprox f) :=
  fun _ _ h => lfpApprox_mono_mid f.dual h
theorem gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_init : f x ≤ x) (h_ab : a ≤ b)
    (h : gfpApprox f x a ∈ fixedPoints f) : gfpApprox f x b = gfpApprox f x a :=
  lfpApprox_eq_of_mem_fixedPoints f.dual x h_init h_ab h
theorem exists_gfpApprox_eq_gfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ gfpApprox f x a = gfpApprox f x b :=
  exists_lfpApprox_eq_lfpApprox f.dual x
lemma gfpApprox_ord_mem_fixedPoint (h_init : f x ≤ x) :
    gfpApprox f x (ord <| succ #α) ∈ fixedPoints f :=
  lfpApprox_ord_mem_fixedPoint f.dual x h_init
lemma le_gfpApprox_of_mem_fixedPoints {a : α}
    (h_a : a ∈ fixedPoints f) (h_le_init : a ≤ x) (i : Ordinal) : a ≤ gfpApprox f x i :=
  lfpApprox_le_of_mem_fixedPoints f.dual x h_a h_le_init i
theorem gfpApprox_ord_eq_gfp : gfpApprox f ⊤ (ord <| succ #α) = f.gfp :=
  lfpApprox_ord_eq_lfp f.dual
theorem gfp_mem_range_gfpApprox : f.gfp ∈ Set.range (gfpApprox f ⊤) :=
  lfp_mem_range_lfpApprox f.dual
end OrdinalApprox