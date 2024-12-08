import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.DiscreteCategory
namespace CategoryTheory
variable {C : Type*}
instance : Groupoid (Discrete C) := { inv := fun h ↦ ⟨⟨h.1.1.symm⟩⟩ }
end CategoryTheory