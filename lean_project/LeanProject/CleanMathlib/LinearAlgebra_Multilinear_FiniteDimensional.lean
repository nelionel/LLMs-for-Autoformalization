import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
namespace MultilinearMap
variable {ι R M₂ : Type*} {M₁ : ι → Type*}
variable [Finite ι]
variable [CommRing R] [AddCommGroup M₂] [Module R M₂]
variable [Module.Finite R M₂] [Module.Free R M₂]
private theorem free_and_finite_fin (n : ℕ) (N : Fin n → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)] :
    Module.Free R (MultilinearMap R N M₂) ∧ Module.Finite R (MultilinearMap R N M₂) := by
  induction' n with n ih
  · haveI : IsEmpty (Fin Nat.zero) := inferInstanceAs (IsEmpty (Fin 0))
    exact
      ⟨Module.Free.of_equiv (constLinearEquivOfIsEmpty R R N M₂),
        Module.Finite.equiv (constLinearEquivOfIsEmpty R R N M₂)⟩
  · suffices
      Module.Free R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) ∧
        Module.Finite R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) by
      cases this
      exact
        ⟨Module.Free.of_equiv (multilinearCurryLeftEquiv R N M₂).symm,
          Module.Finite.equiv (multilinearCurryLeftEquiv R N M₂).symm⟩
    cases ih fun i => N i.succ
    exact ⟨Module.Free.linearMap _ _ _ _, Module.Finite.linearMap _ _ _ _⟩
variable [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
variable [∀ i, Module.Finite R (M₁ i)] [∀ i, Module.Free R (M₁ i)]
private theorem free_and_finite :
    Module.Free R (MultilinearMap R M₁ M₂) ∧ Module.Finite R (MultilinearMap R M₁ M₂) := by
  cases nonempty_fintype ι
  have := @free_and_finite_fin R M₂ _ _ _ _ _ (Fintype.card ι)
    (fun x => M₁ ((Fintype.equivFin ι).symm x))
  cases' this with l r
  have e := domDomCongrLinearEquiv' R R M₁ M₂ (Fintype.equivFin ι)
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
instance _root_.Module.Finite.multilinearMap : Module.Finite R (MultilinearMap R M₁ M₂) :=
  free_and_finite.2
instance _root_.Module.Free.multilinearMap : Module.Free R (MultilinearMap R M₁ M₂) :=
  free_and_finite.1
end MultilinearMap