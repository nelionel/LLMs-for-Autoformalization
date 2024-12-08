import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Basic
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Basic
noncomputable section
open Function
namespace Set
section Enumerate
variable {α : Type*} (sel : Set α → Option α)
def enumerate : Set α → ℕ → Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n
theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate sel s n = none
  | 0 => by simp [h, enumerate]
  | n + 1 => by simp [h, enumerate]
theorem enumerate_eq_none :
    ∀ {s n₁ n₂}, enumerate sel s n₁ = none → n₁ ≤ n₂ → enumerate sel s n₂ = none
  | _, 0, _ => fun h _ ↦ enumerate_eq_none_of_sel sel h
  | s, n + 1, m => fun h hm ↦ by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m with
      | zero => contradiction
      | succ m' =>
        simp? [hs, enumerate] at h ⊢ says
          simp only [enumerate, hs, Option.bind_eq_bind, Option.some_bind] at h ⊢
        have hm : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm
theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) :
    ∀ {s n a}, enumerate sel s n = some a → a ∈ s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s with
    | none => simp [enumerate_eq_none_of_sel, h]
    | some a' =>
      simp only [enumerate, h, Nat.add_eq, add_zero]
      exact fun h' : enumerate sel (s \ {a'}) n = some a ↦
        have : a ∈ s \ {a'} := enumerate_mem h_sel h'
        this.left
theorem enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : Set α} (h_sel : ∀ s a, sel s = some a → a ∈ s)
    (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := by
  rcases le_total n₁ n₂ with (hn|hn)
  on_goal 2 => swap_var n₁ ↔ n₂, h₁ ↔ h₂
  all_goals
    rcases Nat.le.dest hn with ⟨m, rfl⟩
    clear hn
    induction n₁ generalizing s with
    | zero =>
      cases m with
      | zero => rfl
      | succ m =>
        have h' : enumerate sel (s \ {a}) m = some a := by
          simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
        have : a ∈ s \ {a} := enumerate_mem sel h_sel h'
        simp_all [Set.mem_diff_singleton]
    | succ k ih =>
      cases h : sel s with
      | none =>
        simp_all only [add_comm, self_eq_add_left, Nat.add_succ, enumerate_eq_none_of_sel _ h,
          reduceCtorEq]
      | some =>
        simp_all only [add_comm, self_eq_add_left, enumerate, Option.some.injEq,
                       Nat.add_succ, Nat.succ.injEq]
        exact ih h₁ h₂
end Enumerate
end Set