import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
section Ring
namespace Submodule
variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)
open QuotientAddGroup
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff
@[deprecated (since := "2024-08-29")] alias quotientRel_r_def := quotientRel_def
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩
namespace Quotient
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
theorem mk'_eq_mk' {p : Submodule R M} (x : M) :
    @Quotient.mk' _ (quotientRel p) x = mk x :=
  rfl
theorem mk''_eq_mk {p : Submodule R M} (x : M) : (Quotient.mk'' x : M ⧸ p) = mk x :=
  rfl
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x :=
  rfl
protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq
protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)
instance : Zero (M ⧸ p) where
  zero := Quotient.mk'' 0
instance : Inhabited (M ⧸ p) :=
  ⟨0⟩
@[simp]
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl
@[simp]
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)
instance addCommGroup : AddCommGroup (M ⧸ p) :=
  QuotientAddGroup.Quotient.addCommGroup p.toAddSubgroup
@[simp]
theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y :=
  rfl
@[simp]
theorem mk_neg : (mk (-x) : M ⧸ p) = -(mk x) :=
  rfl
@[simp]
theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y :=
  rfl
protected nonrec lemma «forall» {P : M ⧸ p → Prop} : (∀ a, P a) ↔ ∀ a, P (mk a) := Quotient.forall
section SMul
variable {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)
instance instSMul' : SMul S (M ⧸ P) :=
  ⟨fun a =>
    Quotient.map' (a • ·) fun x y h =>
      leftRel_apply.mpr <| by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩
instance instSMul : SMul R (M ⧸ P) :=
  Quotient.instSMul' P
@[simp]
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl
instance smulCommClass (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M]
    [SMulCommClass S T M] : SMulCommClass S T (M ⧸ P) where
  smul_comm _x _y := Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)
instance isScalarTower (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
    [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P) where
  smul_assoc _x _y := Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S (M ⧸ P) where
  op_smul_eq_smul _x := Quotient.ind' fun _z => congr_arg mk <| op_smul_eq_smul _ _
end SMul
section Module
variable {S : Type*}
instance mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : MulAction S (M ⧸ P) :=
  { Function.Surjective.mulAction mk Quot.mk_surjective <| Submodule.Quotient.mk_smul P with
    toSMul := instSMul' _ }
instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P
instance smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M) :
    SMulZeroClass S (M ⧸ P) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ <| Submodule.Quotient.mk_smul P
instance smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P) :=
  Quotient.smulZeroClass' P
instance distribSMul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribSMul S (M ⧸ P) :=
  { Function.Surjective.distribSMul {toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl}
    Quot.mk_surjective (Submodule.Quotient.mk_smul P) with
    toSMulZeroClass := smulZeroClass' _ }
instance distribSMul (P : Submodule R M) : DistribSMul R (M ⧸ P) :=
  Quotient.distribSMul' P
instance distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : DistribMulAction S (M ⧸ P) :=
  { Function.Surjective.distribMulAction {toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl}
    Quot.mk_surjective (Submodule.Quotient.mk_smul P) with
    toMulAction := mulAction' _ }
instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) :=
  { Function.Surjective.module _ {toFun := mk, map_zero' := by rfl, map_add' := fun _ _ => by rfl}
    Quot.mk_surjective (Submodule.Quotient.mk_smul P) with
    toDistribMulAction := distribMulAction' _ }
instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P
end Module
@[elab_as_elim]
theorem induction_on {C : M ⧸ p → Prop} (x : M ⧸ p) (H : ∀ z, C (Submodule.Quotient.mk z)) :
    C x := Quotient.inductionOn' x H
theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩
end Quotient
section
variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
theorem quot_hom_ext (f g : (M ⧸ p) →ₗ[R] M₂) (h : ∀ x : M, f (Quotient.mk x) = g (Quotient.mk x)) :
    f = g :=
  LinearMap.ext fun x => Submodule.Quotient.induction_on _ x h
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp
@[simp]
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl
theorem mkQ_surjective : Function.Surjective p.mkQ := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩
end
variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
@[ext 1100] 
theorem linearMap_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g :=
  LinearMap.ext fun x => Submodule.Quotient.induction_on _ x <| (LinearMap.congr_fun h : _)
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }
@[simp]
theorem quotEquivOfEq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x) :=
  rfl
end Submodule
end Ring