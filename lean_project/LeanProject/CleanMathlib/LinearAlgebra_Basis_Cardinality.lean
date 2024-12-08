import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.SetTheory.Cardinal.Cofinality
section Finite
open Basis Cardinal Set Submodule Finsupp
universe u v w w'
variable {R : Type u} {M : Type v}
section Semiring
variable [Semiring R] [AddCommMonoid M] [Nontrivial R] [Module R M]
lemma basis_finite_of_finite_spans (w : Set M) (hw : w.Finite) (s : span R w = ⊤) {ι : Type w}
    (b : Basis ι R M) : Finite ι := by
  classical
  haveI := hw.to_subtype
  cases nonempty_fintype w
  rw [← not_infinite_iff_finite]
  intro i
  let S : Finset ι := Finset.univ.sup fun x : w => (b.repr x).support
  let bS : Set M := b '' S
  have h : ∀ x ∈ w, x ∈ span R bS := by
    intro x m
    rw [← b.linearCombination_repr x, span_image_eq_map_linearCombination, Submodule.mem_map]
    use b.repr x
    simp only [and_true, eq_self_iff_true, Finsupp.mem_supported]
    rw [Finset.coe_subset, ← Finset.le_iff_subset]
    exact Finset.le_sup (f := fun x : w ↦ (b.repr ↑x).support) (Finset.mem_univ (⟨x, m⟩ : w))
  have k : span R bS = ⊤ := eq_top_iff.2 (le_trans s.ge (span_le.2 h))
  obtain ⟨x, nm⟩ := Infinite.exists_not_mem_finset S
  have k' : b x ∈ span R bS := by
    rw [k]
    exact mem_top
  simp only [self_mem_span_image, Finset.mem_coe, bS] at k'
  exact nm k'
end Semiring
section Ring
variable [Ring R] [AddCommGroup M] [Nontrivial R] [Module R M]
theorem union_support_maximal_linearIndependent_eq_range_basis {ι : Type w} (b : Basis ι R M)
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    ⋃ k, ((b.repr (v k)).support : Set ι) = Set.univ := by
  by_contra h
  simp only [← Ne.eq_def, ne_univ_iff_exists_not_mem, mem_iUnion, not_exists_not,
    Finsupp.mem_support_iff, Finset.mem_coe] at h
  obtain ⟨b', w⟩ := h
  let v' : Option κ → M := fun o => o.elim (b b') v
  have r : range v ⊆ range v' := by
    rintro - ⟨k, rfl⟩
    use some k
    simp only [v', Option.elim_some]
  have r' : b b' ∉ range v := by
    rintro ⟨k, p⟩
    simpa [w] using congr_arg (fun m => (b.repr m) b') p
  have r'' : range v ≠ range v' := by
    intro e
    have p : b b' ∈ range v' := by
      use none
      simp only [v', Option.elim_none]
    rw [← e] at p
    exact r' p
  have i' : LinearIndependent R ((↑) : range v' → M) := by
    apply LinearIndependent.to_subtype_range
    rw [linearIndependent_iff]
    intro l z
    rw [Finsupp.linearCombination_option] at z
    simp only [v', Option.elim'] at z
    change _ + Finsupp.linearCombination R v l.some = 0 at z
    have l₀ : l none = 0 := by
      rw [← eq_neg_iff_add_eq_zero] at z
      replace z := neg_eq_iff_eq_neg.mpr z
      apply_fun fun x => b.repr x b' at z
      simp only [repr_self, map_smul, mul_one, Finsupp.single_eq_same, Pi.neg_apply,
        Finsupp.smul_single', map_neg, Finsupp.coe_neg] at z
      erw [DFunLike.congr_fun (apply_linearCombination R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b']
        at z
      simpa [Finsupp.linearCombination_apply, w] using z
    have l₁ : l.some = 0 := by
      rw [l₀, zero_smul, zero_add] at z
      exact linearIndependent_iff.mp i _ z
    ext (_ | a)
    · simp only [l₀, Finsupp.coe_zero, Pi.zero_apply]
    · erw [DFunLike.congr_fun l₁ a]
      simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [LinearIndependent.Maximal] at m
  specialize m (range v') i' r
  exact r'' m
theorem infinite_basis_le_maximal_linearIndependent' {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    Cardinal.lift.{w'} #ι ≤ Cardinal.lift.{w} #κ := by
  let Φ := fun k : κ => (b.repr (v k)).support
  have w₁ : #ι ≤ #(Set.range Φ) := by
    apply Cardinal.le_range_of_union_finset_eq_top
    exact union_support_maximal_linearIndependent_eq_range_basis b v i m
  have w₂ : Cardinal.lift.{w'} #(Set.range Φ) ≤ Cardinal.lift.{w} #κ := Cardinal.mk_range_le_lift
  exact (Cardinal.lift_le.mpr w₁).trans w₂
theorem infinite_basis_le_maximal_linearIndependent {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #ι ≤ #κ :=
  Cardinal.lift_le.mp (infinite_basis_le_maximal_linearIndependent' b v i m)
end Ring
end Finite