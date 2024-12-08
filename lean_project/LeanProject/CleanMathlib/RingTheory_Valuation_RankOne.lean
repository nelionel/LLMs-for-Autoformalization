import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Valuation.Basic
noncomputable section
open Function Multiplicative
open scoped NNReal
variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace Valuation
class RankOne (v : Valuation R Γ₀) where
  hom : Γ₀ →*₀ ℝ≥0
  strictMono' : StrictMono hom
  nontrivial' : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1
namespace RankOne
variable (v : Valuation R Γ₀) [RankOne v]
lemma strictMono : StrictMono (hom v) := strictMono'
lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := nontrivial'
theorem zero_of_hom_zero {x : Γ₀} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [_root_.map_zero, hx] at hs
  exact hs.false
theorem hom_eq_zero_iff {x : Γ₀} : RankOne.hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, _root_.map_zero]⟩
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.eq_iff, Units.val_one]
  exact ((nontrivial v).choose_spec ).2
end RankOne
end Valuation