import Aesop
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Core
open Lean Elab Meta Term Mathlib.Tactic Syntax
open Lean.Elab.Tactic (liftMetaTactic liftMetaTactic' TacticM getMainGoal)
namespace Mathlib.Tactic.Bound
lemma mul_lt_mul_left_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) : b < c → a * b < a * c :=
  (mul_lt_mul_left a0).mpr
lemma mul_lt_mul_right_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (c0 : 0 < c) : a < b → a * c < b * c :=
  (mul_lt_mul_right c0).mpr
lemma Nat.cast_pos_of_pos {R : Type} [OrderedSemiring R] [Nontrivial R] {n : ℕ} :
    0 < n → 0 < (n : R) :=
  Nat.cast_pos.mpr
lemma Nat.one_le_cast_of_le {α : Type} [AddCommMonoidWithOne α] [PartialOrder α]
    [AddLeftMono α] [ZeroLEOneClass α]
    [CharZero α] {n : ℕ} : 1 ≤ n → 1 ≤ (n : α) :=
  Nat.one_le_cast.mpr
attribute [bound] le_refl
attribute [bound] sq_nonneg Nat.cast_nonneg abs_nonneg Nat.zero_lt_succ pow_pos pow_nonneg
  sub_nonneg_of_le sub_pos_of_lt inv_nonneg_of_nonneg inv_pos_of_pos tsub_pos_of_lt mul_pos
  mul_nonneg div_pos div_nonneg add_nonneg
attribute [bound] Nat.one_le_cast_of_le one_le_mul_of_one_le_of_one_le
attribute [bound] le_abs_self neg_abs_le neg_le_neg tsub_le_tsub_right mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right le_add_of_nonneg_right le_add_of_nonneg_left le_mul_of_one_le_right
  mul_le_of_le_one_right sub_le_sub add_le_add mul_le_mul
attribute [bound] Nat.cast_pos_of_pos neg_lt_neg sub_lt_sub_left sub_lt_sub_right add_lt_add_left
  add_lt_add_right mul_lt_mul_left_of_pos_of_lt mul_lt_mul_right_of_pos_of_lt
attribute [bound] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min max_lt
attribute [bound] zero_le_one zero_lt_one zero_le_two zero_lt_two
attribute [bound_forward] le_of_lt
section Guessing
variable {α : Type} [LinearOrder α] {a b c : α}
lemma le_max_of_le_left_or_le_right : a ≤ b ∨ a ≤ c → a ≤ max b c := le_max_iff.mpr
lemma lt_max_of_lt_left_or_lt_right : a < b ∨ a < c → a < max b c := lt_max_iff.mpr
lemma min_le_of_left_le_or_right_le : a ≤ c ∨ b ≤ c → min a b ≤ c := min_le_iff.mpr
lemma min_lt_of_left_lt_or_right_lt : a < c ∨ b < c → min a b < c := min_lt_iff.mpr
attribute [bound]
  le_max_of_le_left_or_le_right
  lt_max_of_lt_left_or_lt_right
  min_le_of_left_le_or_right_le
  min_lt_of_left_lt_or_right_lt
end Guessing
def boundNormNum : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    let tac := do Mathlib.Meta.NormNum.elabNormNum .missing .missing .missing
    let goals ← Lean.Elab.Tactic.run i.goal tac |>.run'
    if !goals.isEmpty then failure
    return (#[], none, some .hundred)
attribute [aesop unsafe 10% tactic (rule_sets := [Bound])] boundNormNum
def boundLinarith : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    Linarith.linarith false [] {} i.goal
    return (#[], none, some .hundred)
attribute [aesop unsafe 5% tactic (rule_sets := [Bound])] boundLinarith
def boundConfig : Aesop.Options := {
  enableSimp := false
}
end Mathlib.Tactic.Bound
syntax "bound " (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| bound) => do
    let tac ← `(tactic| aesop (rule_sets := [Bound, -default]) (config := Bound.boundConfig))
    liftMetaTactic fun g ↦ do return (← Lean.Elab.runTactic g tac.raw).1
macro_rules
  | `(tactic| bound%$tk [$[$ts],*]) => do
    let haves ← ts.mapM fun (t : Term) => withRef t `(tactic| have := $t)
    `(tactic| ($haves;*; bound%$tk))