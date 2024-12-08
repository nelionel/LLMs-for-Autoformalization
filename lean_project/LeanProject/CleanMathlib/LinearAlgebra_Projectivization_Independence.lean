import Mathlib.LinearAlgebra.Projectivization.Basic
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}
namespace Projectivization
inductive Independent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : LinearIndependent K f) :
    Independent fun i => mk K (f i) (hf i)
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh.units_smul a
    ext i
    exact (ha i).symm
  · convert Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero
theorem independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submodule := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)
@[deprecated (since := "2024-11-24")]
alias independent_iff_completeLattice_independent := independent_iff_iSupIndep
inductive Dependent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬LinearIndependent K f) :
    Dependent fun i => mk K (f i) (hf i)
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose! hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert Dependent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · exact fun i => rep_nonzero (f i)
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]
@[simp]
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2,
    Function.comp_apply, Matrix.cons_val_one, Matrix.head_cons, Ne]
  simp only [Matrix.cons_val_zero, not_and, not_forall, Classical.not_not, Function.comp_apply,
    ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v), mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)
@[simp]
theorem independent_pair_iff_neq (u v : ℙ K V) : Independent ![u, v] ↔ u ≠ v := by
  rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]
end Projectivization