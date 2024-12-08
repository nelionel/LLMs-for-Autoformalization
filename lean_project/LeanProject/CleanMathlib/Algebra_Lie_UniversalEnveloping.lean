import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
universe u₁ u₂ u₃
variable (R : Type u₁) (L : Type u₂)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "ιₜ" => TensorAlgebra.ι R
namespace UniversalEnvelopingAlgebra
inductive Rel : TensorAlgebra R L → TensorAlgebra R L → Prop
  | lie_compat (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)
end UniversalEnvelopingAlgebra
def UniversalEnvelopingAlgebra :=
  RingQuot (UniversalEnvelopingAlgebra.Rel R L)
namespace UniversalEnvelopingAlgebra
instance instInhabited : Inhabited (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Inhabited (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
instance instRing : Ring (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Ring (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
instance instAlgebra : Algebra R (UniversalEnvelopingAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (UniversalEnvelopingAlgebra.Rel R L)))
def mkAlgHom : TensorAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L :=
  RingQuot.mkAlgHom R (Rel R L)
variable {L}
@[simps!] 
def ι : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L :=
  { (mkAlgHom R L).toLinearMap.comp ιₜ with
    map_lie' := fun {x y} => by
      suffices mkAlgHom R L (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) = mkAlgHom R L (ιₜ x * ιₜ y) by
        rw [map_mul] at this; simp [LieRing.of_associative_ring_bracket, ← this]
      exact RingQuot.mkAlgHom_rel _ (Rel.lie_compat x y) }
variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)
def lift : (L →ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) where
  toFun f :=
    RingQuot.liftAlgHom R
      ⟨TensorAlgebra.lift R (f : L →ₗ[R] A), by
        intro a b h; induction h
        simp only [LieRing.of_associative_ring_bracket, map_add, TensorAlgebra.lift_ι_apply,
          LieHom.coe_toLinearMap, LieHom.map_lie, map_mul, sub_add_cancel]⟩
  invFun F := (F : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R)
  left_inv f := by
    ext
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
      UniversalEnvelopingAlgebra.ι_apply, mkAlgHom]
    erw [RingQuot.liftAlgHom_mkAlgHom_apply]
    simp only [TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap]
  right_inv F := by
    apply RingQuot.ringQuot_ext'
    ext
    simp [mkAlgHom]; rfl
@[simp]
theorem lift_symm_apply (F : UniversalEnvelopingAlgebra R L →ₐ[R] A) :
    (lift R).symm F = (F : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R) :=
  rfl
@[simp]
theorem ι_comp_lift : lift R f ∘ ι R = f :=
  funext <| LieHom.ext_iff.mp <| (lift R).symm_apply_apply f
theorem lift_ι_apply (x : L) : lift R f (ι R x) = f x := by
  rw [← Function.comp_apply (f := lift R f) (g := ι R) (x := x), ι_comp_lift]
@[simp]
theorem lift_ι_apply' (x : L) :
    lift R f ((UniversalEnvelopingAlgebra.mkAlgHom R L) (ιₜ x)) = f x := by
  simpa using lift_ι_apply R f x
theorem lift_unique (g : UniversalEnvelopingAlgebra R L →ₐ[R] A) : g ∘ ι R = f ↔ g = lift R f := by
  refine Iff.trans ?_ (lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]
@[ext]
theorem hom_ext {g₁ g₂ : UniversalEnvelopingAlgebra R L →ₐ[R] A}
    (h :
      (g₁ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R) =
        (g₂ : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (ι R)) :
    g₁ = g₂ :=
  have h' : (lift R).symm g₁ = (lift R).symm g₂ := by ext; simp [h]
  (lift R).symm.injective h'
end UniversalEnvelopingAlgebra