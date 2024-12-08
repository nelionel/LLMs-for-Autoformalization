import Mathlib.Algebra.GradedMonoid
variable {ιA ιB ιM : Type*}
namespace GradedMonoid
section Defs
variable (A : ιA → Type*) (M : ιM → Type*)
class GSMul [VAdd ιA ιM] where
  smul {i j} : A i → M j → M (i +ᵥ j)
instance GMul.toGSMul [Add ιA] [GMul A] : GSMul A A where smul := GMul.mul
instance GSMul.toSMul [VAdd ιA ιM] [GSMul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun x y ↦ ⟨_, GSMul.smul x.snd y.snd⟩⟩
theorem mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i +ᵥ j) (GSMul.smul a b) :=
  rfl
class GMulAction [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A] extends GSMul A M where
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
instance GMonoid.toGMulAction [AddMonoid ιA] [GMonoid A] : GMulAction A A :=
  { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
instance GMulAction.toMulAction [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M) where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul
end Defs
end GradedMonoid
section Subobjects
variable {R : Type*}
class SetLike.GradedSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  (A : ιA → S) (B : ιB → N) : Prop where
  smul_mem : ∀ ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i +ᵥ j)
instance SetLike.toGSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] :
    GradedMonoid.GSMul (fun i ↦ A i) fun i ↦ B i where
  smul a b := ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩
@[simp]
theorem SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] {i : ιA} {j : ιB} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ιA ιB (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.1 • y.1 :=
  rfl
instance SetLike.GradedMul.toGradedSMul [AddMonoid ιA] [Monoid R] {S : Type*} [SetLike S R]
    (A : ιA → S) [SetLike.GradedMonoid A] : SetLike.GradedSMul A A where
  smul_mem _ _ _ _ hi hj := SetLike.GradedMonoid.toGradedMul.mul_mem hi hj
end Subobjects
section HomogeneousElements
variable {S R N M : Type*} [SetLike S R] [SetLike N M]
theorem SetLike.Homogeneous.graded_smul [VAdd ιA ιB] [SMul R M] {A : ιA → S} {B : ιB → N}
    [SetLike.GradedSMul A B] {a : R} {b : M} :
    SetLike.Homogeneous A a → SetLike.Homogeneous B b → SetLike.Homogeneous B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i +ᵥ j, SetLike.GradedSMul.smul_mem hi hj⟩
end HomogeneousElements