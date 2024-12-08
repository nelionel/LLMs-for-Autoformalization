import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
structure MonomialOrder (σ : Type*) where
  syn : Type*
  locacm : LinearOrderedCancelAddCommMonoid syn := by infer_instance
  toSyn : (σ →₀ ℕ) ≃+ syn
  toSyn_monotone : Monotone toSyn
  wf : WellFoundedLT syn := by infer_instance
attribute [instance] MonomialOrder.locacm MonomialOrder.wf
namespace MonomialOrder
variable {σ : Type*} (m : MonomialOrder σ)
lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add
instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by
    have := m.le_add_right 0 (m.toSyn.symm a)
    simp [map_add, zero_add] at this
    exact this
@[simp]
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl
theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff
lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective
scoped
notation:25 c "≺[" m:25 "]" d:25 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)
scoped
notation:25 c "≼[" m:25 "]" d:25 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)
end MonomialOrder
section Lex
open Finsupp
open scoped MonomialOrder
noncomputable instance {α N : Type*} [LinearOrder α] [OrderedCancelAddCommMonoid N] :
    OrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa only [add_le_add_iff_left] using h
theorem Finsupp.lex_lt_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i :=
    Finsupp.lex_def
theorem Finsupp.lex_le_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a ≤ b ↔ a = b ∨ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i := by
    rw [le_iff_eq_or_lt, Finsupp.lex_lt_iff]
example : toLex (Finsupp.single 0 2) > toLex (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  use 0; simp
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 1) := by
  use 0; simp
example : toLex (Finsupp.single 1 1) < toLex (Finsupp.single 0 2) := by
  use 0; simp
variable {σ : Type*} [LinearOrder σ]
noncomputable def MonomialOrder.lex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  toSyn :=
  { toEquiv := toLex
    map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone
theorem MonomialOrder.lex_le_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≼[lex] d ↔ toLex c ≤ toLex d := Iff.rfl
theorem MonomialOrder.lex_lt_iff [WellFoundedGT σ] {c d : σ →₀ ℕ} :
    c ≺[lex] d ↔ toLex c < toLex d := Iff.rfl
end Lex