import Mathlib.CategoryTheory.Category.Basic
universe u v
namespace CategoryTheory
@[nolint unusedArguments]
def KleisliCat (_ : Type u → Type v) :=
  Type u
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α
instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := α → m β
  id _ x := pure x
  comp f g := f >=> g
instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  refine funext (fun x => ?_) <;>
  simp (config := { unfoldPartialApp := true }) [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]
@[simp]
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = @pure m _ α :=
  rfl
theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl
instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩
instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩
end CategoryTheory