import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
assert_not_exists FiniteDimensional
open Metric Topology
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace PadicInt
theorem totallyBounded_univ : TotallyBounded (Set.univ : Set ℤ_[p]) := by
  refine Metric.totallyBounded_iff.mpr (fun ε hε ↦ ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ ↦ ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk
instance compactSpace : CompactSpace ℤ_[p] := by
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ p, complete_univ⟩
end PadicInt
namespace Padic
instance : ProperSpace ℚ_[p] := by
  suffices LocallyCompactSpace ℚ_[p] from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  have : closedBall 0 1 ∈ 𝓝 (0 : ℚ_[p]) := closedBall_mem_nhds _ zero_lt_one
  simp only [closedBall, dist_eq_norm_sub, sub_zero] at this
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_ this
  simpa only [isCompact_iff_compactSpace] using PadicInt.compactSpace p
end Padic