import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.FiniteType
universe u v
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
open Polynomial
def reesAlgebra : Subalgebra R R[X] where
  carrier := { f | ∀ i, f.coeff i ∈ I ^ i }
  mul_mem' hf hg i := by
    rw [coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    rw [← Finset.mem_antidiagonal.mp e, pow_add]
    exact Ideal.mul_mem_mul (hf j) (hg k)
  one_mem' i := by
    rw [coeff_one]
    split_ifs with h
    · subst h
      simp
    · simp
  add_mem' hf hg i := by
    rw [coeff_add]
    exact Ideal.add_mem _ (hf i) (hg i)
  zero_mem' _ := Ideal.zero_mem _
  algebraMap_mem' r i := by
    rw [algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
theorem mem_reesAlgebra_iff (f : R[X]) : f ∈ reesAlgebra I ↔ ∀ i, f.coeff i ∈ I ^ i :=
  Iff.rfl
theorem mem_reesAlgebra_iff_support (f : R[X]) :
    f ∈ reesAlgebra I ↔ ∀ i ∈ f.support, f.coeff i ∈ I ^ i := by
  apply forall_congr'
  intro a
  rw [mem_support_iff, Iff.comm, Classical.imp_iff_right_iff, Ne, ← imp_iff_not_or]
  exact fun e => e.symm ▸ (I ^ a).zero_mem
theorem reesAlgebra.monomial_mem {I : Ideal R} {i : ℕ} {r : R} :
    monomial i r ∈ reesAlgebra I ↔ r ∈ I ^ i := by
  simp +contextual [mem_reesAlgebra_iff_support, coeff_monomial, ←
    imp_iff_not_or]
theorem monomial_mem_adjoin_monomial {I : Ideal R} {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    monomial n r ∈ Algebra.adjoin R (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
  induction' n with n hn generalizing r
  · exact Subalgebra.algebraMap_mem _ _
  · rw [pow_succ'] at hr
    apply Submodule.smul_induction_on
      (p := fun r => (monomial (Nat.succ n)) r ∈ Algebra.adjoin R (Submodule.map (monomial 1) I)) hr
    · intro r hr s hs
      rw [Nat.succ_eq_one_add, smul_eq_mul, ← monomial_mul_monomial]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_image_of_mem _ hr)) (hn hs)
    · intro x y hx hy
      rw [monomial_add]
      exact Subalgebra.add_mem _ hx hy
theorem adjoin_monomial_eq_reesAlgebra :
    Algebra.adjoin R (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) = reesAlgebra I := by
  apply le_antisymm
  · apply Algebra.adjoin_le _
    rintro _ ⟨r, hr, rfl⟩
    exact reesAlgebra.monomial_mem.mpr (by rwa [pow_one])
  · intro p hp
    rw [p.as_sum_support]
    apply Subalgebra.sum_mem _ _
    rintro i -
    exact monomial_mem_adjoin_monomial (hp i)
variable {I}
theorem reesAlgebra.fg (hI : I.FG) : (reesAlgebra I).FG := by
  classical
    obtain ⟨s, hs⟩ := hI
    rw [← adjoin_monomial_eq_reesAlgebra, ← hs]
    use s.image (monomial 1)
    rw [Finset.coe_image]
    change
      _ =
        Algebra.adjoin R
          (Submodule.map (monomial 1 : R →ₗ[R] R[X]) (Submodule.span R ↑s) : Set R[X])
    rw [Submodule.map_span, Algebra.adjoin_span]
instance [IsNoetherianRing R] : Algebra.FiniteType R (reesAlgebra I) :=
  ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg <| IsNoetherian.noetherian I)⟩
instance [IsNoetherianRing R] : IsNoetherianRing (reesAlgebra I) :=
  Algebra.FiniteType.isNoetherianRing R _