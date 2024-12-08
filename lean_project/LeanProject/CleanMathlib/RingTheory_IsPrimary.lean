import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
open Pointwise
namespace Submodule
section CommSemiring
variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
protected def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S
variable {S : Submodule R M}
lemma IsPrimary.ne_top (h : S.IsPrimary) : S ≠ ⊤ := h.left
end CommSemiring
section CommRing
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}
lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ S), x ≠ 0 → r • x = 0 →
      ∃ n : ℕ, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  refine (and_congr_right fun _ ↦ ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm, ← or_iff_not_imp_left,
    ← LinearMap.range_eq_top.mpr S.mkQ_surjective, ← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]
end CommRing
end Submodule