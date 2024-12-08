import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
open Filter Topology
namespace NonarchimedeanGroup
variable {α G : Type*}
variable [CommGroup G] [UniformSpace G] [UniformGroup G] [NonarchimedeanGroup G]
@[to_additive "Let `G` be a nonarchimedean additive abelian group, and let `f : α → G` be a function
that tends to zero on the filter of cofinite sets. For each finite subset of `α`, consider the
partial sum of `f` on that subset. These partial sums form a Cauchy filter."]
theorem cauchySeq_prod_of_tendsto_cofinite_one {f : α → G} (hf : Tendsto f cofinite (𝓝 1)) :
    CauchySeq (fun s ↦ ∏ i ∈ s, f i) := by
  apply cauchySeq_finset_iff_prod_vanishing.mpr
  intro U hU
  rcases is_nonarchimedean U hU with ⟨V, hV⟩
  use (tendsto_def.mp hf V V.mem_nhds_one).toFinset
  intro t ht
  apply hV
  apply Subgroup.prod_mem
  intro i hi
  simpa using Finset.disjoint_left.mp ht hi
@[to_additive "Let `G` be a complete nonarchimedean additive abelian group, and let `f : α → G` be a
function that tends to zero on the filter of cofinite sets. Then `f` is unconditionally summable."]
theorem multipliable_of_tendsto_cofinite_one [CompleteSpace G] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f :=
  CompleteSpace.complete (cauchySeq_prod_of_tendsto_cofinite_one hf)
@[to_additive "Let `G` be a complete nonarchimedean additive abelian group. Then a function
`f : α → G` is unconditionally summable if and only if it tends to zero on the filter of cofinite
sets."]
theorem multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α → G) :
    Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨Multipliable.tendsto_cofinite_one, multipliable_of_tendsto_cofinite_one⟩
end NonarchimedeanGroup