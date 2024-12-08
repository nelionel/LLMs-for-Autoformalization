import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Quotient
namespace Ideal
open scoped DirectSum
variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsPrincipalIdealRing R] [IsDomain S] [Finite ι]
noncomputable def quotientEquivPiSpan (I : Ideal S) (b : Basis ι R S) (hI : I ≠ ⊥) :
    (S ⧸ I) ≃ₗ[R] ∀ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) := by
  haveI := Fintype.ofFinite ι
  let a := I.smithCoeffs b hI
  let b' := I.ringBasis b hI
  let ab := I.selfBasis b hI
  have ab_eq := I.selfBasis_def b hI
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i := by
    intro x
    rw [ab.mem_ideal_iff']
    simp_rw [ab_eq]
    have : ∀ (c : ι → R) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← MulAction.mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, this c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
  let I' : Submodule R (ι → R) := Submodule.pi Set.univ fun i => span ({a i} : Set R)
  have : Submodule.map (b'.equivFun : S →ₗ[R] ι → R) (I.restrictScalars R) = I' := by
    ext x
    simp only [I', Submodule.mem_map, Submodule.mem_pi, mem_span_singleton, Set.mem_univ,
      Submodule.restrictScalars_mem, mem_I_iff, smul_eq_mul, forall_true_left, LinearEquiv.coe_coe,
      Basis.equivFun_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i
    · rintro hdvd
      refine ⟨∑ i, x i • b' i, fun i => ?_, ?_⟩ <;> rw [b'.repr_sum_self]
      · exact hdvd i
  refine ((Submodule.Quotient.restrictScalarsEquiv R I).restrictScalars R).symm.trans
    (σ₁₂ := RingHom.id R) (σ₃₂ := RingHom.id R) (re₂₃ := inferInstance) (re₃₂ := inferInstance) ?_
  refine (Submodule.Quotient.equiv (I.restrictScalars R) I' b'.equivFun this).trans
    (σ₁₂ := RingHom.id R) (σ₃₂ := RingHom.id R) (re₂₃ := inferInstance) (re₃₂ := inferInstance) ?_
  classical
    let this :=
      Submodule.quotientPi (show _ → Submodule R R from fun i => span ({a i} : Set R))
    exact this
noncomputable def quotientEquivPiZMod (I : Ideal S) (b : Basis ι ℤ S) (hI : I ≠ ⊥) :
    S ⧸ I ≃+ ∀ i, ZMod (I.smithCoeffs b hI i).natAbs :=
  let a := I.smithCoeffs b hI
  let e := I.quotientEquivPiSpan b hI
  let e' : (∀ i : ι, ℤ ⧸ span ({a i} : Set ℤ)) ≃+ ∀ i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (S ⧸ I) ≃ₗ[ℤ] _) : S ⧸ I ≃+ _).trans e'
noncomputable def fintypeQuotientOfFreeOfNeBot [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) (hI : I ≠ ⊥) : Fintype (S ⧸ I) := by
  let b := Module.Free.chooseBasis ℤ S
  let a := I.smithCoeffs b hI
  let e := I.quotientEquivPiZMod b hI
  haveI : ∀ i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (smithCoeffs_ne_zero b I hI i)⟩
  classical exact Fintype.ofEquiv (∀ i, ZMod (a i).natAbs) e.symm
variable (F : Type*) [CommRing F] [Algebra F R] [Algebra F S] [IsScalarTower F R S]
  (b : Basis ι R S) {I : Ideal S} (hI : I ≠ ⊥)
noncomputable def quotientEquivDirectSum :
    (S ⧸ I) ≃ₗ[F] ⨁ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) := by
  haveI := Fintype.ofFinite ι
  exact ((I.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm
theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R S) [Nontrivial F]
    [∀ i, Module.Free F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))]
    [∀ i, Module.Finite F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))] :
    Module.finrank F (S ⧸ I) =
      ∑ i, Module.finrank F (R ⧸ span ({I.smithCoeffs b hI i} : Set R)) := by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI, Module.finrank_directSum]
end Ideal