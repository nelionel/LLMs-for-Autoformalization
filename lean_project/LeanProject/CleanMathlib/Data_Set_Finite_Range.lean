import Mathlib.Data.Fintype.Card
import Mathlib.Data.ULift
assert_not_exists OrderedRing
assert_not_exists MonoidWithZero
open Set Function
universe u v w x
variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}
namespace Set
section FintypeInstances
instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (PLift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) <| by simp
end FintypeInstances
end Set
namespace Finite.Set
open scoped Classical
instance finite_range (f : ι → α) [Finite ι] : Finite (range f) := by
  haveI := Fintype.ofFinite (PLift ι)
  infer_instance
instance finite_replacement [Finite α] (f : α → β) :
    Finite {f x | x : α} :=
  Finite.Set.finite_range f
end Finite.Set
namespace Set
section SetFiniteConstructors
theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _
theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    {y : β | ∃ x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2
end SetFiniteConstructors
end Set