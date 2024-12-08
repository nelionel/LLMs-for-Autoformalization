import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Ring.Basic
universe uM
variable {M : Type uM}
namespace AddMonoid.End
instance instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.End M) where
  natCast n := n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1
@[simp]
lemma natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl
@[simp] lemma ofNat_apply [AddCommMonoid M] (n : ℕ) [n.AtLeastTwo] (m : M) :
    (no_index (OfNat.ofNat n : AddMonoid.End M)) m = n • m := rfl
instance instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  { AddMonoid.End.monoid M, AddMonoidHom.addCommMonoid, AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl }
instance instRing [AddCommGroup M] : Ring (AddMonoid.End M) :=
  { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }
end AddMonoid.End
section Semiring
variable {R S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' a b := AddMonoidHom.ext <| add_mul a b
theorem AddMonoidHom.mul_apply (x y : R) : AddMonoidHom.mul x y = x * y :=
  rfl
@[simp]
theorem AddMonoidHom.coe_mul : ⇑(AddMonoidHom.mul : R →+ R →+ R) = AddMonoidHom.mulLeft :=
  rfl
@[simp]
theorem AddMonoidHom.coe_flip_mul :
    ⇑(AddMonoidHom.mul : R →+ R →+ R).flip = AddMonoidHom.mulRight :=
  rfl
theorem AddMonoidHom.map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (AddMonoidHom.mul : R →+ R →+ R).compr₂ f = (AddMonoidHom.mul.comp f).compl₂ f :=
  Iff.symm AddMonoidHom.ext_iff₂
lemma AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute {a : R} :
    mulLeft a = mulRight a ↔ ∀ b, Commute a b :=
  DFunLike.ext_iff
lemma AddMonoidHom.mulRight_eq_mulLeft_iff_forall_commute {b : R} :
    mulRight b = mulLeft b ↔ ∀ a, Commute a b :=
  DFunLike.ext_iff
@[simps!]
def AddMonoid.End.mulLeft : R →+ AddMonoid.End R :=
  AddMonoidHom.mul
@[simps!]
def AddMonoid.End.mulRight : R →+ AddMonoid.End R :=
  (AddMonoidHom.mul : R →+ AddMonoid.End R).flip
end Semiring
section CommSemiring
variable {R : Type*} [NonUnitalNonAssocCommSemiring R]
namespace AddMonoid.End
lemma mulRight_eq_mulLeft : mulRight = (mulLeft : R →+ AddMonoid.End R) :=
  AddMonoidHom.ext fun _ =>
    Eq.symm <| AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)
end AddMonoid.End
end CommSemiring