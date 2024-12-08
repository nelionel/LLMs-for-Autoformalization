import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.TraceForm
variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]
namespace LieAlgebra
class IsKilling : Prop where
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥
attribute [simp] IsKilling.killingCompl_top_eq_bot
namespace IsKilling
variable [IsKilling R L]
@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]
lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  simp [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
variable {R L} in
lemma ideal_eq_bot_of_isLieAbelian
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
    (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian
instance instSemisimple [IsKilling K L] [Module.Finite K L] : IsSemisimple K L := by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
    exact h₁.1 <| IsKilling.ideal_eq_bot_of_isLieAbelian I
instance instHasTrivialRadical
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    HasTrivialRadical R L :=
  (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian
end IsKilling
section LieEquiv
variable {R L}
variable {L' : Type*} [LieRing L'] [LieAlgebra R L']
@[simp] lemma killingForm_of_equiv_apply (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    killingForm R L' (e x) (e y) = killingForm R L x y := by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']
lemma isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L' := by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' ↦ ?_, fun hx y _ ↦ hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' ∈ LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa [map_zero] using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : ∀ y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'
alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv
end LieEquiv
end LieAlgebra