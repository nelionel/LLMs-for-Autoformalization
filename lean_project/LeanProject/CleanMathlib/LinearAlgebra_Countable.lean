import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
noncomputable section
namespace Finsupp
variable {M : Type*} {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
instance {ι : Type*} [Countable R] [Countable ι] (v : ι → M) :
    Countable (Submodule.span R (Set.range v)) := by
  refine Set.countable_coe_iff.mpr (Set.Countable.mono ?_ (Set.countable_range
      (fun c : (ι →₀ R) => c.sum fun i _ => (c i) • v i)))
  exact fun _ h => Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp h)
end Finsupp