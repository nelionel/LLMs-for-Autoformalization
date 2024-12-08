import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Weight
import Mathlib.Logic.Equiv.TransferInstance
section degLex
def DegLex (α : Type*) := α
variable {α : Type*}
@[match_pattern] def toDegLex : α ≃ DegLex α := Equiv.refl _
theorem toDegLex_injective : Function.Injective (toDegLex (α := α)) := fun _ _ ↦ _root_.id
theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b := Iff.rfl
@[match_pattern] def ofDegLex : DegLex α ≃ α := Equiv.refl _
theorem ofDegLex_injective : Function.Injective (ofDegLex (α := α)) := fun _ _ ↦ _root_.id
theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b := Iff.rfl
@[simp] theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex := rfl
@[simp] theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex := rfl
@[simp] theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a := rfl
@[simp] theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a := rfl
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegLex.rec {β : DegLex α → Sort*} (h : ∀ a, β (toDegLex a)) :
    ∀ a, β a := fun a => h (ofDegLex a)
@[simp] lemma DegLex.forall_iff {p : DegLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegLex a) := Iff.rfl
@[simp] lemma DegLex.exists_iff {p : DegLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegLex a) := Iff.rfl
noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegLex α) := ofDegLex.addCommMonoid
theorem toDegLex_add [AddCommMonoid α] (a b : α) :
    toDegLex (a + b) = toDegLex a + toDegLex b := rfl
theorem ofDegLex_add [AddCommMonoid α] (a b : DegLex α) :
    ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl
namespace Finsupp
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))
theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl
namespace DegLex
theorem wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)
instance [LT α] : LT (DegLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩
theorem lt_def [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl
theorem lt_iff [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp only [lt_def, Prod.Lex.lt_iff]
variable [LinearOrder α]
instance isStrictOrder : IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) where
  irrefl := fun a ↦ by simp [lt_def]
  trans := by
    intro a b c hab hbc
    simp only [lt_iff] at hab hbc ⊢
    rcases hab with (hab | hab)
    · rcases hbc with (hbc | hbc)
      · left; exact lt_trans hab hbc
      · left; exact lt_of_lt_of_eq hab hbc.1
    · rcases hbc with (hbc | hbc)
      · left; exact lt_of_eq_of_lt hab.1 hbc
      · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩
instance : LinearOrder (DegLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)
theorem le_iff {x y : DegLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) ≤ toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]
noncomputable instance : OrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegLex_add, degree_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegLex_add, degree_add] using h
noncomputable instance :
    LinearOrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  le_total := instLinearOrderDegLexNat.le_total
  decidableLE := instLinearOrderDegLexNat.decidableLE
  compare_eq_compareOfLessAndEq := instLinearOrderDegLexNat.compare_eq_compareOfLessAndEq
theorem single_strictAnti : StrictAnti (fun (a : α) ↦ toDegLex (single a 1)) := by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]
theorem single_antitone : Antitone (fun (a : α) ↦ toDegLex (single a 1)) :=
  single_strictAnti.antitone
theorem single_lt_iff {a b : α} :
    toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_lt
theorem single_le_iff {a b : α} :
    toDegLex (Finsupp.single b 1) ≤ toDegLex (Finsupp.single a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_le
theorem monotone_degree :
    Monotone (fun (x : DegLex (α →₀ ℕ)) ↦ (ofDegLex x).degree) := by
  intro x y
  rw [le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1
instance orderBot : OrderBot (DegLex (α →₀ ℕ)) where
  bot := toDegLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [le_iff, ofDegLex_toDegLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or, ge_iff_le]
      exact bot_le
    · simp [h]
instance wellFoundedLT [WellFoundedGT α] :
    WellFoundedLT (DegLex (α →₀ ℕ)) :=
  ⟨wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩
end DegLex
end Finsupp
namespace MonomialOrder
open Finsupp
variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
noncomputable def degLex :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegLex.le_iff, ofDegLex_toDegLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ (not_lt.mp ha), toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, degree_add]
      exact Nat.le_add_right a.degree (b - a).degree
theorem degLex_le_iff {a b : σ →₀ ℕ} :
    a ≼[degLex] b ↔ toDegLex a ≤ toDegLex b :=
  Iff.rfl
theorem degLex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[degLex] b ↔ toDegLex a < toDegLex b :=
  Iff.rfl
theorem degLex_single_le_iff {a b : σ} :
    single a 1 ≼[degLex] single b 1 ↔ b ≤ a := by
  rw [MonomialOrder.degLex_le_iff, DegLex.single_le_iff]
theorem degLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degLex] single b 1 ↔ b < a := by
  rw [MonomialOrder.degLex_lt_iff, DegLex.single_lt_iff]
end MonomialOrder
section Examples
open Finsupp MonomialOrder DegLex
example : single (1 : Fin 2) 1 ≺[degLex] single 0 1 := by
  rw [degLex_lt_iff, single_lt_iff]
  exact Nat.one_pos
example : (single 0 1 + single 1 1) ≺[degLex] single (0 : Fin 2) 2  := by
  simp only [degLex_lt_iff, lt_iff, ofDegLex_toDegLex, degree_add,
    degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp
example : single (0 : Fin 2) 1 ≺[degLex] single 1 2 := by
  simp [degLex_lt_iff, lt_iff]
end Examples
end degLex