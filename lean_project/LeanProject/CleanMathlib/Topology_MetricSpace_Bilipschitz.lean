import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
open NNReal
section Uniformity
open Uniformity
variable {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
variable {K₁ K₂ : ℝ≥0} {f : α → β}
lemma uniformity_eq_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) :
    𝓤[(inferInstance : UniformSpace β).comap f] = 𝓤 α :=
  hf₁.isUniformInducing hf₂.uniformContinuous |>.comap_uniformity
end Uniformity
section Bornology
open Bornology Filter
variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
variable {K₁ K₂ : ℝ≥0} {f : α → β}
lemma bornology_eq_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) :
    @cobounded _ (induced f) = cobounded α :=
  le_antisymm hf₂.comap_cobounded_le hf₁.tendsto_cobounded.le_comap
lemma isBounded_iff_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f)
    (s : Set α) : @IsBounded _ (induced f) s ↔ Bornology.IsBounded s :=
  Filter.ext_iff.1 (bornology_eq_of_bilipschitz hf₁ hf₂) (sᶜ)
end Bornology