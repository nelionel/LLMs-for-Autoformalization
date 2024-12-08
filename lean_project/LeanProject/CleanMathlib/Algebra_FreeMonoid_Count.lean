import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
variable {α : Type*} (p : α → Prop) [DecidablePred p]
namespace FreeAddMonoid
def countP : FreeAddMonoid α →+ ℕ where
  toFun := List.countP p
  map_zero' := List.countP_nil _
  map_add' := List.countP_append _
theorem countP_of (x : α) : countP p (of x) = if p x = true then 1 else 0 := by
  simp [countP, List.countP, List.countP.go]
theorem countP_apply (l : FreeAddMonoid α) : countP p l = List.countP p l := rfl
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)
theorem count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  simp [Pi.single, Function.update, count, countP, List.countP, List.countP.go,
    Bool.beq_eq_decide_eq]
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = List.count x l :=
  rfl
end FreeAddMonoid
namespace FreeMonoid
def countP : FreeMonoid α →* Multiplicative ℕ :=
    AddMonoidHom.toMultiplicative (FreeAddMonoid.countP p)
theorem countP_of' (x : α) :
    countP p (of x) = if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
    erw [FreeAddMonoid.countP_of]
    simp only [eq_iff_iff, iff_true, ofAdd_zero]; rfl
theorem countP_of (x : α) : countP p (of x) = if p x then Multiplicative.ofAdd 1 else 1 := by
  rw [countP_of', ofAdd_zero]
theorem countP_apply (l : FreeAddMonoid α) : countP p l = Multiplicative.ofAdd (List.countP p l) :=
  rfl
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (List.count x l) := rfl
theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = @Pi.mulSingle α (fun _ => Multiplicative ℕ) _ _ x (Multiplicative.ofAdd 1) y :=
  by simp [count, countP_of, Pi.mulSingle_apply, eq_comm, Bool.beq_eq_decide_eq]
end FreeMonoid