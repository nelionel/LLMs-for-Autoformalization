import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Antidiagonal
namespace Finsupp
open Finset
universe u
variable {α : Type u} [DecidableEq α]
def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  Multiset.toFinsupp
    ((Finsupp.toMultiset f).antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp))
instance instHasAntidiagonal : HasAntidiagonal (α →₀ ℕ) where
  antidiagonal f := f.antidiagonal'.support
  mem_antidiagonal {f} {p} := by
    rcases p with ⟨p₁, p₂⟩
    simp [antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
    ← Multiset.toFinsupp_eq_iff (f := f)]
@[simp]
theorem antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = singleton (0, 0) := rfl
@[to_additive]
theorem prod_antidiagonal_swap {M : Type*} [CommMonoid M] (n : α →₀ ℕ)
    (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
    ∏ p ∈ antidiagonal n, f p.1 p.2 = ∏ p ∈ antidiagonal n, f p.2 p.1 :=
  prod_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp)
@[simp]
theorem antidiagonal_single (a : α) (n : ℕ) :
    antidiagonal (single a n) = (antidiagonal n).map
      (Function.Embedding.prodMap ⟨_, single_injective a⟩ ⟨_, single_injective a⟩) := by
  ext ⟨x, y⟩
  simp only [mem_antidiagonal, mem_map, mem_antidiagonal, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    refine ⟨x a, y a, DFunLike.congr_fun h a |>.trans single_eq_same, ?_⟩
    simp_rw [DFunLike.ext_iff, ← forall_and]
    intro i
    replace h := DFunLike.congr_fun h i
    simp_rw [single_apply, Finsupp.add_apply] at h ⊢
    obtain rfl | hai := Decidable.eq_or_ne a i
    · exact ⟨if_pos rfl, if_pos rfl⟩
    · simp_rw [if_neg hai, add_eq_zero] at h ⊢
      exact h.imp Eq.symm Eq.symm
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact (single_add _ _ _).symm
end Finsupp