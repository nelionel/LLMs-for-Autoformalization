import Mathlib.FieldTheory.Fixed
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.LinearIndependent
namespace groupCohomology
namespace Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
noncomputable def aux (f : (L ≃ₐ[K] L) → Lˣ) : L → L :=
  Finsupp.linearCombination L (fun φ : L ≃ₐ[K] L ↦ (φ : L → L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
theorem aux_ne_zero (f : (L ≃ₐ[K] L) → Lˣ) : aux f ≠ 0 :=
  have : LinearIndependent L (fun (f : L ≃ₐ[K] L) => (f : L → L)) :=
    LinearIndependent.comp (ι' := L ≃ₐ[K] L)
      (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)
end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
theorem isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units
    (f : (L ≃ₐ[K] L) → Lˣ) (hf : IsMulOneCocycle f) :
    IsMulOneCoboundary f := by
  obtain ⟨z, hz⟩ : ∃ z, aux f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero f <| funext <| fun x => H x)
  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.linearCombination, Finsupp.sum_fintype]
  use (Units.mk0 (aux f z) hz)⁻¹
  intro g
  simp only [IsMulOneCocycle, IsMulOneCoboundary, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))
end
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
  uniq := fun a => Quotient.inductionOn' a fun x => (Submodule.Quotient.mk_eq_zero _).2 <| by
    refine (oneCoboundariesOfIsMulOneCoboundary ?_).2
    rcases isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units x.1
      (isMulOneCocycle_of_oneCocycles x) with ⟨β, hβ⟩
    use β
end groupCohomology