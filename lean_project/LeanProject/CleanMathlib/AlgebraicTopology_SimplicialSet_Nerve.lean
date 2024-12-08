import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ComposableArrows
open CategoryTheory.Category Simplicial
universe v u
namespace CategoryTheory
@[simps]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f x := x.whiskerLeft (SimplexCategory.toCat.map f.unop)
instance {C : Type*} [Category C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (ComposableArrows C (Δ.unop.len)))
@[simps]
def nerveFunctor : Cat.{v, u} ⥤ SSet where
  obj C := nerve C
  map F := { app := fun _ => (F.mapComposableArrows _).obj }
namespace Nerve
variable {C : Type*} [Category C] {n : ℕ}
lemma δ₀_eq {x : nerve C _[n + 1]} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl
end Nerve
end CategoryTheory