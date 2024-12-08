import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Opposite
variable {F : Type*} (R : Type*)
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  involution' : ∀ x, (toFun (toFun x).unop).unop = x
add_decl_doc RingInvo.toRingEquiv
class RingInvoClass (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ]
  extends RingEquivClass F R Rᵐᵒᵖ : Prop where
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x
@[coe]
def RingInvoClass.toRingInvo {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoClass F R] (f : F) :
    RingInvo R :=
  { (f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }
namespace RingInvo
variable {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ]
instance [RingInvoClass F R] : CoeTC F (RingInvo R) :=
  ⟨RingInvoClass.toRingInvo⟩
instance : EquivLike (RingInvo R) R Rᵐᵒᵖ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
instance : RingInvoClass (RingInvo R) R where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun _ => MulOpposite.unop_injective <| involution _
    involution' := involution }
@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x
@[norm_cast]
theorem coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff
end RingInvo
open RingInvo
section CommRing
variable [CommRing R]
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun _ => rfl }
instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩
end CommRing