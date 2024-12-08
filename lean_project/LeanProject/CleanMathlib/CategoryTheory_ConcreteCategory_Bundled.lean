import Mathlib.Init
import Batteries.Tactic.Lint.Misc
universe u v
namespace CategoryTheory
variable {c d : Type u → Type v}
structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α := by infer_instance
namespace Bundled
attribute [coe] α
set_option checkBinderAnnotations false in
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩
instance coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩
theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl
abbrev map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩
end Bundled
end CategoryTheory