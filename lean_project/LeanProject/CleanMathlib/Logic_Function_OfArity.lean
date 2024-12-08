import Mathlib.Logic.Function.FromTypes
universe u
namespace Function
abbrev OfArity (α β : Type u) (n : ℕ) : Type u := FromTypes (fun (_ : Fin n) => α) β
@[simp]
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β := fromTypes_zero _ _
@[simp]
theorem ofArity_succ (α β : Type u) (n : ℕ) :
    OfArity α β n.succ = (α → OfArity α β n) := fromTypes_succ _ _
namespace OfArity
def const (α : Type u) {β : Type u} (b : β) (n : ℕ) : OfArity α β n :=
  FromTypes.const (fun _ => α) b
@[simp]
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  FromTypes.const_zero (fun _ => α) b
@[simp]
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : ℕ) :
    const α b n.succ = fun _ => const _ b n :=
  FromTypes.const_succ (fun _ => α) b
theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : ℕ) (x : α) :
    const α b n.succ x = const _ b n := FromTypes.const_succ_apply _ b x
instance inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))
end OfArity
namespace FromTypes
lemma fromTypes_fin_const (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β = OfArity α β n := rfl
def fromTypes_fin_const_equiv (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β ≃ OfArity α β n := .refl _
end FromTypes
end Function