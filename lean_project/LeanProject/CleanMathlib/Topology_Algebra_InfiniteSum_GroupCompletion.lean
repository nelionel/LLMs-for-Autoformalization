import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.InfiniteSum.Group
open UniformSpace.Completion
variable {α β : Type*} [AddCommGroup α] [UniformSpace α] [UniformAddGroup α]
theorem hasSum_iff_hasSum_compl (f : β → α) (a : α) :
    HasSum (toCompl ∘ f) a ↔ HasSum f a := (isDenseInducing_toCompl α).hasSum_iff f a
theorem summable_iff_summable_compl_and_tsum_mem (f : β → α) :
    Summable f ↔ Summable (toCompl ∘ f) ∧ ∑' i, toCompl (f i) ∈ Set.range toCompl :=
  (isDenseInducing_toCompl α).summable_iff_tsum_comp_mem_range f
theorem summable_iff_cauchySeq_finset_and_tsum_mem (f : β → α) :
    Summable f ↔ CauchySeq (fun s : Finset β ↦ ∑ b in s, f b) ∧
      ∑' i, toCompl (f i) ∈ Set.range toCompl := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← map_sum]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum
theorem Summable.toCompl_tsum {f : β → α} (hf : Summable f) : ∑' i, toCompl (f i) = ∑' i, f i :=
  (hf.map_tsum toCompl (continuous_coe α)).symm