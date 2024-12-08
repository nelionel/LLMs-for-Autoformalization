import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
namespace Ideal
section IsPrincipal
variable {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R}
noncomputable
def quotEquivPowQuotPowSucc (h : I.IsPrincipal) (h': I ≠ ⊥) (n : ℕ) :
    (R ⧸ I) ≃ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
  let f : (I ^ n : Ideal R) →ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
    Submodule.mkQ _
  let ϖ := h.principal'.choose
  have hI : I = Ideal.span {ϖ} := h.principal'.choose_spec
  have hϖ : ϖ ^ n ∈ I ^ n := hI ▸ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
  let g : R →ₗ[R] (I ^ n : Ideal R) := (LinearMap.mulRight R ϖ^n).codRestrict _ fun x ↦ by
    simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply, Ideal.submodule_span_eq]
    exact Ideal.mul_mem_left _ _ hϖ
  have : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul,
      f, g]
    constructor <;> intro hx
    · exact Submodule.mul_mem_mul hx hϖ
    · rw [← pow_succ', hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm, pow_succ, mul_assoc, mul_right_inj' (pow_ne_zero _ _)] at hy
      · rw [hI, Ideal.mem_span_singleton]
        exact ⟨y, hy⟩
      · contrapose! h'
        rw [hI, h', Ideal.span_singleton_eq_bot]
  let e : (R ⧸ I) ≃ₗ[R] R ⧸ (LinearMap.ker (f.comp g)) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f ∘ₗ g)) this
  refine e.trans ((f.comp g).quotKerEquivOfSurjective ?_)
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨x, hx⟩
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  refine hx.imp ?_
  simp [g, LinearMap.codRestrict, eq_comm, mul_comm]
noncomputable
def quotEquivPowQuotPowSuccEquiv (h : I.IsPrincipal) (h': I ≠ ⊥) (n : ℕ) :
    (R ⧸ I) ≃ (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
  quotEquivPowQuotPowSucc h h' n
end IsPrincipal
end Ideal