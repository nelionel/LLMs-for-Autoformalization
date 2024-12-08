import Mathlib.Algebra.Ring.Equiv
variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
class RingHomId {R : Type*} [Semiring R] (σ : R →+* R) : Prop where
  eq_id : σ = RingHom.id R
instance {R : Type*} [Semiring R] : RingHomId (RingHom.id R) where
  eq_id := rfl
class RingHomCompTriple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : outParam (R₁ →+* R₃)) :
  Prop where
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃
attribute [simp] RingHomCompTriple.comp_eq
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
namespace RingHomCompTriple
@[simp]
theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
  RingHom.congr_fun comp_eq x
end RingHomCompTriple
class RingHomInvPair (σ : R₁ →+* R₂) (σ' : outParam (R₂ →+* R₁)) : Prop where
  comp_eq : σ'.comp σ = RingHom.id R₁
  comp_eq₂ : σ.comp σ' = RingHom.id R₂
variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}
namespace RingHomInvPair
variable [RingHomInvPair σ σ']
theorem comp_apply_eq {x : R₁} : σ' (σ x) = x := by
  rw [← RingHom.comp_apply, comp_eq]
  simp
theorem comp_apply_eq₂ {x : R₂} : σ (σ' x) = x := by
  rw [← RingHom.comp_apply, comp_eq₂]
  simp
instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  ⟨rfl, rfl⟩
instance triples {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁) :=
  ⟨by simp only [comp_eq]⟩
instance triples₂ {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₂₁ σ₁₂ (RingHom.id R₂) :=
  ⟨by simp only [comp_eq₂]⟩
theorem of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ →+* R₂) ↑e.symm :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩
theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ :=
  ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩
end RingHomInvPair
namespace RingHomCompTriple
instance ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  ⟨by
    ext
    simp⟩
instance right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂ :=
  ⟨by
    ext
    simp⟩
end RingHomCompTriple
class RingHomSurjective (σ : R₁ →+* R₂) : Prop where
  is_surjective : Function.Surjective σ
theorem RingHom.surjective (σ : R₁ →+* R₂) [t : RingHomSurjective σ] : Function.Surjective σ :=
  t.is_surjective
namespace RingHomSurjective
instance (priority := 100) invPair {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁} [RingHomInvPair σ₁ σ₂] :
    RingHomSurjective σ₁ :=
  ⟨fun x => ⟨σ₂ x, RingHomInvPair.comp_apply_eq₂⟩⟩
instance ids : RingHomSurjective (RingHom.id R₁) :=
  ⟨is_surjective⟩
theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ :=
  { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }
instance (σ : R₁ ≃+* R₂) : RingHomSurjective (σ : R₁ →+* R₂) := ⟨σ.surjective⟩
end RingHomSurjective