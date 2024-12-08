import Mathlib.RingTheory.PrincipalIdealDomain
variable {R : Type*} [CommRing R]
namespace Ideal
open Submodule Associates
open scoped nonZeroDivisors
variable (R) in
def isPrincipalSubmonoid : Submonoid (Ideal R) where
  carrier := {I | IsPrincipal I}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, span_singleton_mul_span_singleton x y⟩
  one_mem' := ⟨1, one_eq_span⟩
theorem mem_isPrincipalSubmonoid_iff {I : Ideal R} :
    I ∈ isPrincipalSubmonoid R ↔ IsPrincipal I := Iff.rfl
theorem span_singleton_mem_isPrincipalSubmonoid (a : R) :
    span {a} ∈ isPrincipalSubmonoid R := mem_isPrincipalSubmonoid_iff.mpr ⟨a, rfl⟩
variable (R) in
def isPrincipalNonZeroDivisorsSubmonoid : Submonoid (Ideal R)⁰ where
  carrier := {I | IsPrincipal I.val}
  mul_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by
      simp_rw [Submonoid.mk_mul_mk, submodule_span_eq, span_singleton_mul_span_singleton]⟩
  one_mem' := ⟨1, by simp⟩
variable [IsDomain R]
variable (R) in
noncomputable def associatesEquivIsPrincipal :
    Associates R ≃ {I : Ideal R // IsPrincipal I} where
  toFun := _root_.Quotient.lift (fun x ↦ ⟨span {x}, x, rfl⟩)
    (fun _ _ _ ↦ by simpa [span_singleton_eq_span_singleton])
  invFun I := .mk I.2.generator
  left_inv := Quotient.ind fun _ ↦ by simpa using
    Ideal.span_singleton_eq_span_singleton.mp (@Ideal.span_singleton_generator _ _ _ ⟨_, rfl⟩)
  right_inv I := by simp only [_root_.Quotient.lift_mk, span_singleton_generator, Subtype.coe_eta]
@[simp]
theorem associatesEquivIsPrincipal_apply (x : R) :
    associatesEquivIsPrincipal R (.mk x) = span {x} := rfl
@[simp]
theorem associatesEquivIsPrincipal_symm_apply {I : Ideal R} (hI : IsPrincipal I) :
    (associatesEquivIsPrincipal R).symm ⟨I, hI⟩ = .mk hI.generator := rfl
theorem associatesEquivIsPrincipal_mul (x y : Associates R) :
    (associatesEquivIsPrincipal R (x * y) : Ideal R) =
      (associatesEquivIsPrincipal R x) * (associatesEquivIsPrincipal R y) := by
  rw [← quot_out x, ← quot_out y]
  simp_rw [mk_mul_mk, associatesEquivIsPrincipal_apply, span_singleton_mul_span_singleton]
@[simp]
theorem associatesEquivIsPrincipal_map_zero :
    (associatesEquivIsPrincipal R 0 : Ideal R) = 0 := by
  rw [← mk_zero, associatesEquivIsPrincipal_apply, Submodule.zero_eq_bot, span_singleton_eq_bot]
@[simp]
theorem associatesEquivIsPrincipal_map_one :
    (associatesEquivIsPrincipal R 1 : Ideal R) = 1 := by
  rw [one_eq_mk_one, associatesEquivIsPrincipal_apply, span_singleton_one, one_eq_top]
variable (R) in
noncomputable def associatesMulEquivIsPrincipal :
    Associates R ≃* (isPrincipalSubmonoid R) where
  __ := associatesEquivIsPrincipal R
  map_mul' _ _ := by
    erw [Subtype.ext_iff, associatesEquivIsPrincipal_mul]
    rfl
variable (R) in
noncomputable def associatesNonZeroDivisorsEquivIsPrincipal :
    Associates R⁰ ≃ {I : (Ideal R)⁰ // IsPrincipal (I : Ideal R)} :=
  calc Associates R⁰ ≃ (Associates R)⁰ := associatesNonZeroDivisorsEquiv.toEquiv.symm
    _ ≃ {I : {I : Ideal R // IsPrincipal I} // I.1 ∈ (Ideal R)⁰} :=
      Equiv.subtypeEquiv (associatesEquivIsPrincipal R)
        (fun x ↦ by rw [← quot_out x, mk_mem_nonZeroDivisors_associates,
          associatesEquivIsPrincipal_apply, span_singleton_nonZeroDivisors])
    _ ≃ {I : Ideal R // IsPrincipal I ∧ I ∈ (Ideal R)⁰} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ IsPrincipal I) (fun I ↦ I ∈ (Ideal R)⁰)
    _ ≃ {I : Ideal R // I ∈ (Ideal R)⁰ ∧ IsPrincipal I} := Equiv.setCongr (by simp_rw [and_comm])
    _ ≃ {I : (Ideal R)⁰ // IsPrincipal I.1} := (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
@[simp]
theorem associatesNonZeroDivisorsEquivIsPrincipal_apply (x : R⁰) :
    associatesNonZeroDivisorsEquivIsPrincipal R (.mk x) = Ideal.span {(x : R)} := rfl
theorem associatesNonZeroDivisorsEquivIsPrincipal_coe (x : Associates R⁰) :
    (associatesNonZeroDivisorsEquivIsPrincipal R x : Ideal R) =
      (associatesEquivIsPrincipal R (associatesNonZeroDivisorsEquiv.symm x)) := rfl
theorem associatesNonZeroDivisorsEquivIsPrincipal_mul (x y : Associates R⁰) :
    (associatesNonZeroDivisorsEquivIsPrincipal R (x * y) : Ideal R) =
      (associatesNonZeroDivisorsEquivIsPrincipal R x) *
        (associatesNonZeroDivisorsEquivIsPrincipal R y) := by
  simp_rw [associatesNonZeroDivisorsEquivIsPrincipal_coe, _root_.map_mul, Submonoid.coe_mul,
    associatesEquivIsPrincipal_mul]
@[simp]
theorem associatesNonZeroDivisorsEquivIsPrincipal_map_one :
    (associatesNonZeroDivisorsEquivIsPrincipal R 1 : Ideal R) = 1 := by
  rw [associatesNonZeroDivisorsEquivIsPrincipal_coe, map_one, OneMemClass.coe_one,
    associatesEquivIsPrincipal_map_one]
variable (R) in
noncomputable def associatesNonZeroDivisorsMulEquivIsPrincipal :
    Associates R⁰ ≃* (isPrincipalNonZeroDivisorsSubmonoid R) where
  __ := associatesNonZeroDivisorsEquivIsPrincipal R
  map_mul' _ _ := by
    erw [Subtype.ext_iff, Subtype.ext_iff, associatesNonZeroDivisorsEquivIsPrincipal_mul]
    rfl
end Ideal