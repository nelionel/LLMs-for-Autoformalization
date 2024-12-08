import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}
namespace List
@[deprecated (since := "2024-08-10")] alias all_iff_forall := all_eq_true
theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp
@[deprecated (since := "2024-08-10")] alias any_iff_exists := any_eq_true
theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp
theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_eq_true.2 ⟨_, h₁, h₂⟩
end List