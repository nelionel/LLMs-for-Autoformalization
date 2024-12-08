import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Ring.Defs
open Function
@[to_additive "If `M` additively acts on `α`, then `DomAddAct M` acts on `α → β` as
well as some bundled maps from `α`. This is a type synonym for `AddOpposite M`, so this corresponds
to a right action of `M`."]
def DomMulAct (M : Type*) := MulOpposite M
@[inherit_doc] postfix:max "ᵈᵐᵃ" => DomMulAct
@[inherit_doc] postfix:max "ᵈᵃᵃ" => DomAddAct
namespace DomMulAct
variable {M : Type*}
@[to_additive "Equivalence between `M` and `Mᵈᵐᵃ`."]
def mk : M ≃ Mᵈᵐᵃ := MulOpposite.opEquiv
set_option hygiene false in
run_cmd
  for n in [`Mul, `One, `Inv, `Semigroup, `CommSemigroup, `LeftCancelSemigroup,
    `RightCancelSemigroup, `MulOneClass, `Monoid, `CommMonoid, `LeftCancelMonoid,
    `RightCancelMonoid, `CancelMonoid, `CancelCommMonoid, `InvolutiveInv, `DivInvMonoid,
    `InvOneClass, `DivInvOneMonoid, `DivisionMonoid, `DivisionCommMonoid, `Group,
    `CommGroup, `NonAssocSemiring, `NonUnitalSemiring, `NonAssocSemiring, `Semiring,
    `Ring, `CommRing].map Lean.mkIdent do
  Lean.Elab.Command.elabCommand (← `(
    @[to_additive] instance [$n Mᵐᵒᵖ] : $n Mᵈᵐᵃ := ‹_›
  ))
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsLeftCancelMul Mᵐᵒᵖ] : IsLeftCancelMul Mᵈᵐᵃ := ‹_›
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsRightCancelMul Mᵐᵒᵖ] : IsRightCancelMul Mᵈᵐᵃ := ‹_›
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsCancelMul Mᵐᵒᵖ] : IsCancelMul Mᵈᵐᵃ := ‹_›
@[to_additive (attr := simp)]
lemma mk_one [One M] : mk (1 : M) = 1 := rfl
@[to_additive (attr := simp)]
lemma symm_mk_one [One M] : mk.symm (1 : Mᵈᵐᵃ) = 1 := rfl
@[to_additive (attr := simp)]
lemma mk_mul [Mul M] (a b : M) : mk (a * b) = mk b * mk a := rfl
@[to_additive (attr := simp)]
lemma symm_mk_mul [Mul M] (a b : Mᵈᵐᵃ) : mk.symm (a * b) = mk.symm b * mk.symm a := rfl
@[to_additive (attr := simp)]
lemma mk_inv [Inv M] (a : M) : mk (a⁻¹) = (mk a)⁻¹ := rfl
@[to_additive (attr := simp)]
lemma symm_mk_inv [Inv M] (a : Mᵈᵐᵃ) : mk.symm (a⁻¹) = (mk.symm a)⁻¹ := rfl
@[to_additive (attr := simp)]
lemma mk_pow [Monoid M] (a : M) (n : ℕ) : mk (a ^ n) = mk a ^ n := rfl
@[to_additive (attr := simp)]
lemma symm_mk_pow [Monoid M] (a : Mᵈᵐᵃ) (n : ℕ) : mk.symm (a ^ n) = mk.symm a ^ n := rfl
@[to_additive (attr := simp)]
lemma mk_zpow [DivInvMonoid M] (a : M) (n : ℤ) : mk (a ^ n) = mk a ^ n := rfl
@[to_additive (attr := simp)]
lemma symm_mk_zpow [DivInvMonoid M] (a : Mᵈᵐᵃ) (n : ℤ) : mk.symm (a ^ n) = mk.symm a ^ n := rfl
variable {β α N : Type*}
@[to_additive]
instance [SMul M α] : SMul Mᵈᵐᵃ (α → β) where
  smul c f a := f (mk.symm c • a)
@[to_additive]
theorem smul_apply [SMul M α] (c : Mᵈᵐᵃ) (f : α → β) (a : α) : (c • f) a = f (mk.symm c • a) := rfl
@[to_additive]
instance [SMul M α] [SMul N β] : SMulCommClass Mᵈᵐᵃ N (α → β) where
  smul_comm _ _ _ := rfl
@[to_additive]
instance [SMul M α] [SMul N β] : SMulCommClass N Mᵈᵐᵃ (α → β) where
  smul_comm _ _ _ := rfl
@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α → β) where
  smul_comm _ _ f := funext fun _ ↦ congr_arg f (smul_comm _ _ _).symm
@[to_additive]
instance [SMul M α] [FaithfulSMul M α] [Nontrivial β] : FaithfulSMul Mᵈᵐᵃ (α → β) where
  eq_of_smul_eq_smul {c₁ c₂} h := mk.symm.injective <| eq_of_smul_eq_smul fun a : α ↦ by
    rcases exists_pair_ne β with ⟨x, y, hne⟩
    contrapose! hne
    haveI := Classical.decEq α
    replace h := congr_fun (h (update (const α x) (mk.symm c₂ • a) y)) a
    simpa [smul_apply, hne] using h
instance [SMul M α] [Zero β] : SMulZeroClass Mᵈᵐᵃ (α → β) where
  smul_zero _ := rfl
instance {A : Type*} [SMul M α] [AddZeroClass A] : DistribSMul Mᵈᵐᵃ (α → A) where
  smul_add _ _ _ := rfl
@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction Mᵈᵐᵃ (α → β) where
  one_smul f := funext fun _ ↦ congr_arg f (one_smul _ _)
  mul_smul _ _ f := funext fun _ ↦ congr_arg f (mul_smul _ _ _)
instance {A : Type*} [Monoid M] [MulAction M α] [AddMonoid A] : DistribMulAction Mᵈᵐᵃ (α → A) where
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
instance {A : Type*} [Monoid M] [MulAction M α] [Monoid A] : MulDistribMulAction Mᵈᵐᵃ (α → A) where
  smul_mul _ _ _ := rfl
  smul_one _ := rfl
section MonoidHom
variable {M M' A B : Type*} [Monoid M] [Monoid A] [MulDistribMulAction M A] [MulOneClass B]
instance : SMul Mᵈᵐᵃ (A →* B) where
  smul c f := f.comp (MulDistribMulAction.toMonoidHom _ (mk.symm c))
instance [Monoid M'] [MulDistribMulAction M' A] [SMulCommClass M M' A] :
    SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A →* B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
theorem smul_monoidHom_apply (c : Mᵈᵐᵃ) (f : A →* B) (a : A) : (c • f) a = f (mk.symm c • a) :=
  rfl
@[simp]
theorem mk_smul_monoidHom_apply (c : M) (f : A →* B) (a : A) : (mk c • f) a = f (c • a) := rfl
instance : MulAction Mᵈᵐᵃ (A →* B) := DFunLike.coe_injective.mulAction (⇑) fun _ _ ↦ rfl
end MonoidHom
section AddMonoidHom
section DistribSMul
variable {A B M M' : Type*} [AddMonoid A] [DistribSMul M A] [AddZeroClass B]
instance : SMul Mᵈᵐᵃ (A →+ B) where
  smul c f := f.comp (DistribSMul.toAddMonoidHom _ (mk.symm c))
instance [DistribSMul M' A] [SMulCommClass M M' A] : SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A →+ B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance [DistribSMul M' B] : SMulCommClass Mᵈᵐᵃ M' (A →+ B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
theorem smul_addMonoidHom_apply (c : Mᵈᵐᵃ) (f : A →+ B) (a : A) : (c • f) a = f (mk.symm c • a) :=
  rfl
@[simp]
theorem mk_smul_addMonoidHom_apply (c : M) (f : A →+ B) (a : A) : (mk c • f) a = f (c • a) := rfl
theorem coe_smul_addMonoidHom (c : Mᵈᵐᵃ) (f : A →+ B) : ⇑(c • f) = c • ⇑f :=
  rfl
end DistribSMul
variable {A M B : Type*}
instance [Monoid M] [AddMonoid A] [DistribMulAction M A] [AddZeroClass B] :
    MulAction Mᵈᵐᵃ (A →+ B) := DFunLike.coe_injective.mulAction (⇑) fun _ _ ↦ rfl
instance [Monoid M] [AddMonoid A] [DistribMulAction M A] [AddCommMonoid B] :
    DistribMulAction Mᵈᵐᵃ (A →+ B) :=
  DFunLike.coe_injective.distribMulAction (AddMonoidHom.coeFn A B) fun _ _ ↦ rfl
instance [Monoid M] [Monoid A] [MulDistribMulAction M A] [CommMonoid B] :
    MulDistribMulAction Mᵈᵐᵃ (A →* B) :=
  DFunLike.coe_injective.mulDistribMulAction (MonoidHom.coeFn A B) fun _ _ ↦ rfl
end AddMonoidHom
end DomMulAct