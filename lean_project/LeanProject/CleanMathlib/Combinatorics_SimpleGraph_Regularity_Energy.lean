import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Rat.BigOperators
open Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]
namespace Finpartition
def energy : ℚ :=
  ((∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : ℚ) / (#P.parts : ℚ) ^ 2
theorem energy_nonneg : 0 ≤ P.energy G := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| sq_nonneg _
theorem energy_le_one : P.energy G ≤ 1 :=
  div_le_of_le_mul₀ (sq_nonneg _) zero_le_one <|
    calc
      ∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 ≤ #P.parts.offDiag • (1 : ℚ) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
          (sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 <| G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul_one_eq_cast _
      _ ≤ _ := by
        rw [offDiag_card, one_mul]
        norm_cast
        rw [sq]
        exact tsub_le_self
@[simp, norm_cast]
theorem coe_energy {𝕜 : Type*} [LinearOrderedField 𝕜] : (P.energy G : 𝕜) =
    (∑ uv ∈ P.parts.offDiag, (G.edgeDensity uv.1 uv.2 : 𝕜) ^ 2) / (#P.parts : 𝕜) ^ 2 := by
  rw [energy]; norm_cast
end Finpartition