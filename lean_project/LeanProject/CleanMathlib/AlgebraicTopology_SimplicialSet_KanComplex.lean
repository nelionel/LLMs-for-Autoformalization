import Mathlib.AlgebraicTopology.SimplicialSet.Basic
namespace SSet
open CategoryTheory Simplicial
class KanComplex (S : SSet) : Prop where
  hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ
end SSet