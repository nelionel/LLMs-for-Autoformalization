import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
noncomputable section

theorem exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Subgroup G} (hP : IsPGroup p P) (H : Subgroup G)
  (hH : P ≤ H) : IsPGroup p H :=
begin
  -- Assume that `P` is a Sylow p-subgroup of `G`
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hP,
  have h₁ : nat.coprime (cardinal.mk (G ⧸ P)) p,
  { rw ← hp2,
    exact finrank_eq_card_div' P.to_subgroup },
  
  -- By assumption, `H` contains `P`, so we look at the subgroup lattice
  have h₂ : cardinal.mk (G ⧸ P) = cardinal.mk (G ⧸ H) * cardinal.mk (H ⧸ P),
  { rw [QuotientGroup.index_eq_card_subgroup H, 
        QuotientGroup.index_eq_card_subgroup P, 
        QuotientGroup.index_eq_card_subgroup (P.comap H.subtype)], 
    simp },
  
  -- Since `p` doesn't divide the index `[G : P]`,
  -- it also doesn't divide the index `[H : P]`
  have h₃ : nat.coprime (cardinal.mk (H ⧸ P)) p,
  { rw ← h₂,
    exact h₁.coprime_dvd_right (dvd_mul_right _ _), },
  
  -- Thus, `P` is a Sylow p-subgroup of `H`
  refine ⟨⟨nat.prime.is_prime hp3, 
    cardinal.mk (H ⧸ P),
    h₃.symm ▸ hp2 ▸ λ q hq, _⟩, h₃ ⟩,
  
  -- Provide details for the Sylow subgroup condition
  simp at *,
  intros hq1 hq2,
  exact hp1 hq2 hq1,
end