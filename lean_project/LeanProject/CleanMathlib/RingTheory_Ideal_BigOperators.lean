import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.RingTheory.Ideal.Defs
universe u v w
variable {α : Type u} {β : Type v} {F : Type w}
namespace Ideal
variable [Semiring α] (I : Ideal α) {a b : α}
theorem sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι → α} :
    (∀ c ∈ t, f c ∈ I) → (∑ i ∈ t, f i) ∈ I :=
  Submodule.sum_mem I
end Ideal