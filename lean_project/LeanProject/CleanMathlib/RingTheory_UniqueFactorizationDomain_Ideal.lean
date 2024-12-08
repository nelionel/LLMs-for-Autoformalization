import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
variable {α : Type*}
open UniqueFactorizationMonoid in
theorem Ideal.IsPrime.exists_mem_prime_of_ne_bot {R : Type*} [CommSemiring R] [IsDomain R]
    [UniqueFactorizationMonoid R] {I : Ideal R} (hI₂ : I.IsPrime) (hI : I ≠ ⊥) :
    ∃ x ∈ I, Prime x := by
  classical
  obtain ⟨a : R, ha₁ : a ∈ I, ha₂ : a ≠ 0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  replace ha₁ : (factors a).prod ∈ I := by
    obtain ⟨u : Rˣ, hu : (factors a).prod * u = a⟩ := factors_prod ha₂
    rwa [← hu, mul_unit_mem_iff_mem _ u.isUnit] at ha₁
  obtain ⟨p : R, hp₁ : p ∈ factors a, hp₂ : p ∈ I⟩ :=
    (hI₂.multiset_prod_mem_iff_exists_mem <| factors a).1 ha₁
  exact ⟨p, hp₂, prime_of_factor p hp₁⟩
section Ideal
lemma Ideal.setOf_isPrincipal_wellFoundedOn_gt [CommSemiring α] [WfDvdMonoid α] [IsDomain α] :
    {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·) := by
  have : {I : Ideal α | I.IsPrincipal} = ((fun a ↦ Ideal.span {a}) '' Set.univ) := by
    ext
    simp [Submodule.isPrincipal_iff, eq_comm]
  rw [this, Set.wellFoundedOn_image, Set.wellFoundedOn_univ]
  convert wellFounded_dvdNotUnit (α := α)
  ext
  exact Ideal.span_singleton_lt_span_singleton
lemma WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt [CommSemiring α] [IsDomain α]
    (h : {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    WfDvdMonoid α := by
  have : WellFounded (α := {I : Ideal α // I.IsPrincipal}) (· > ·) := h
  constructor
  convert InvImage.wf (fun a => ⟨Ideal.span ({a} : Set α), _, rfl⟩) this
  ext
  exact Ideal.span_singleton_lt_span_singleton.symm
end Ideal