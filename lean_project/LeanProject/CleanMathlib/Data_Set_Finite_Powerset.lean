import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
assert_not_exists OrderedRing
assert_not_exists MonoidWithZero
open Set Function
universe u v w x
variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}
namespace Set
section SetFiniteConstructors
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b ⊆ a }.Finite := by
  convert ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset
protected theorem Finite.powerset {s : Set α} (h : s.Finite) : (𝒫 s).Finite :=
  h.finite_subsets
end SetFiniteConstructors
end Set