import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint
open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization
namespace OnePoint
variable (K : Type*) [DivisionRing K] [DecidableEq K]
def equivProjectivization :
    OnePoint K ≃ ℙ K (K × K) where
  toFun p := p.elim (mk K (1, 0) (by simp)) (fun t ↦ mk K (t, 1) (by simp))
  invFun p := by
    refine Projectivization.lift
      (fun u : {v : K × K // v ≠ 0} ↦ if u.1.2 = 0 then ∞ else ((u.1.2)⁻¹ * u.1.1)) ?_ p
    rintro ⟨-, hv⟩ ⟨⟨x, y⟩, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hv
    by_cases h₀ : y = 0 <;> simp [h₀, ht, mul_assoc]
  left_inv p := by cases p <;> simp
  right_inv p := by
    induction' p using ind with p hp
    obtain ⟨x, y⟩ := p
    by_cases h₀ : y = 0 <;> simp only [mk_eq_mk_iff', h₀, Projectivization.lift_mk, if_true,
      if_false, OnePoint.elim_infty, OnePoint.elim_some, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul,
      mul_zero, and_true]
    · use x⁻¹
      simp_all
    · exact ⟨y⁻¹, rfl, inv_mul_cancel₀ h₀⟩
@[simp]
lemma equivProjectivization_apply_infinity :
    equivProjectivization K ∞ = mk K ⟨1, 0⟩ (by simp) :=
  rfl
@[simp]
lemma equivProjectivization_apply_coe (t : K) :
    equivProjectivization K t = mk K ⟨t, 1⟩ (by simp) :=
  rfl
@[simp]
lemma equivProjectivization_symm_apply_mk (x y : K) (h : (x, y) ≠ 0) :
    (equivProjectivization K).symm (mk K ⟨x, y⟩ h) = if y = 0 then ∞ else y⁻¹ * x := by
  simp [equivProjectivization]
end OnePoint