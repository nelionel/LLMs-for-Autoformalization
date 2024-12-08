import Mathlib.RingTheory.TensorProduct.Basic
open TensorProduct
attribute [local instance] TensorProduct.Algebra.module
namespace Subbimodule
section Algebra
variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]
variable [SMulCommClass A B M]
@[simps]
def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
    (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : Submodule (A ⊗[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simpa only [zero_smul] using p.zero_mem)
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] using p.add_mem (hz hm) (hw hm) }
theorem smul_mem (p : Submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p := by
  suffices a • m = a ⊗ₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]
theorem smul_mem' (p : Submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p := by
  suffices b • m = (1 : A) ⊗ₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]
@[simps!]
def baseChange (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
    [IsScalarTower S A M] [IsScalarTower S B M] (p : Submodule (A ⊗[R] B) M) :
    Submodule (A ⊗[S] B) M :=
  mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)
@[simps]
def toSubmodule (p : Submodule (A ⊗[R] B) M) : Submodule A M :=
  { p with
    carrier := p
    smul_mem' := smul_mem p }
@[simps]
def toSubmodule' (p : Submodule (A ⊗[R] B) M) : Submodule B M :=
  { p with
    carrier := p
    smul_mem' := smul_mem' p }
end Algebra
section Ring
variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module S M] [SMulCommClass R S M]
@[simps!]
def toSubbimoduleInt (p : Submodule (R ⊗[ℕ] S) M) : Submodule (R ⊗[ℤ] S) M :=
  baseChange ℤ p
@[simps!]
def toSubbimoduleNat (p : Submodule (R ⊗[ℤ] S) M) : Submodule (R ⊗[ℕ] S) M :=
  baseChange ℕ p
end Ring
end Subbimodule