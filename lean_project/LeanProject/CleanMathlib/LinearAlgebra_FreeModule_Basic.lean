import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Matrix.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Small.Basic
universe u v w z
variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)
open TensorProduct DirectSum
section Basic
variable [Semiring R] [AddCommMonoid M] [Module R M]
class Module.Free : Prop where
  exists_basis : Nonempty <| (I : Type v) × Basis I R M
theorem Module.free_iff_set : Module.Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun h => ⟨Set.range h.exists_basis.some.2, ⟨Basis.reindexRange h.exists_basis.some.2⟩⟩,
    fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩
theorem Module.free_def [Small.{w,v} M] :
    Module.Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) :=
  ⟨fun h =>
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩,
    fun h => ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩⟩
variable {R M}
theorem Module.Free.of_basis {ι : Type w} (b : Basis ι R M) : Module.Free R M :=
  (Module.free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩
end Basic
namespace Module.Free
section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid N] [Module R N]
def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some
noncomputable def repr : M ≃ₗ[R] ChooseBasisIndex R M →₀ R :=
  (chooseBasis R M).repr
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S
instance (priority := 100) noZeroSMulDivisors [NoZeroDivisors R] : NoZeroSMulDivisors R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.noZeroSMulDivisors
instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty
theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right
variable {R M N}
theorem of_equiv (e : M ≃ₗ[R] N) : Module.Free R N :=
  of_basis <| (chooseBasis R M).map e
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') [Module.Free R M] :
    Module.Free R' M' := by
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I →₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I →₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I →₀ R') :=
    { __ := e, map_smul' := fun m x ↦ Finsupp.ext fun i ↦ by simp [he, map_smulₛₗ] }
  exact of_basis (.ofRepr e')
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma iff_of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ ↦ of_ringEquiv e₁ e₂, fun _ ↦ of_ringEquiv e₁.symm e₂.symm⟩
variable (R M N)
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)
instance prod [Module.Free R N] : Module.Free R (M × N) :=
  of_basis <| (chooseBasis R M).prod (chooseBasis R N)
instance pi (M : ι → Type*) [Finite ι] [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]
    [∀ i : ι, Module.Free R (M i)] : Module.Free R (∀ i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
  of_basis <| Pi.basis fun i => chooseBasis R (M i)
instance matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _
instance ulift [Free R M] : Free R (ULift M) := of_equiv ULift.moduleEquiv.symm
variable (ι)
instance function [Finite ι] : Module.Free R (ι → M) :=
  Free.pi _ _
instance finsupp : Module.Free R (ι →₀ M) :=
  of_basis (Finsupp.basis fun _ => chooseBasis R M)
variable {ι}
instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis.{u,z,z} (Basis.empty N : Basis PEmpty R N)
instance (priority := 100) of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N
instance dfinsupp {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
  of_basis <| DFinsupp.basis fun i => chooseBasis R (M i)
instance directSum {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M
end Semiring
section CommSemiring
variable {S} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [Module.Free S M]
  [AddCommMonoid N] [Module R N] [Module.Free R N]
instance tensor : Module.Free S (M ⊗[R] N) :=
  let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)
end CommSemiring
end Module.Free