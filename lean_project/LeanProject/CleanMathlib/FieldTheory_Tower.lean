import Mathlib.RingTheory.Noetherian.Basic
universe u v w u₁ v₁ w₁
open Cardinal Submodule
variable (F : Type u) (K : Type v) (A : Type w)
namespace Module.Finite
variable [Ring F] [Ring K] [Module F K]
  [AddCommGroup A] [Module K A] [NoZeroSMulDivisors K A]
  [Module F A] [IsNoetherian F A] [IsScalarTower F K A] in
theorem left [Nontrivial A] : Module.Finite F K :=
  let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K ℕ A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)
variable [Semiring F] [Semiring K] [Module F K]
  [AddCommMonoid A] [Module K A] [Module F A] [IsScalarTower F K A] in
@[stacks 09G5]
theorem right [hf : Module.Finite F A] : Module.Finite K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b, Submodule.restrictScalars_injective F _ _ <| by
    rw [Submodule.restrictScalars_top, eq_top_iff, ← hb, Submodule.span_le]
    exact Submodule.subset_span⟩⟩
end Module.Finite
alias FiniteDimensional.left := Module.Finite.left
alias FiniteDimensional.right := Module.Finite.right