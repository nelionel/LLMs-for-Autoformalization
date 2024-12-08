import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.UniformSpace.Equiv
def WithCStarModule (E : Type*) := E
namespace WithCStarModule
@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ" => WithCStarModule
section Basic
variable (R R' E : Type*)
def equiv : WithCStarModule E ≃ E := Equiv.refl _
instance instNontrivial [Nontrivial E] : Nontrivial (WithCStarModule E) := ‹Nontrivial E›
instance instInhabited [Inhabited E] : Inhabited (WithCStarModule E) := ‹Inhabited E›
instance instNonempty [Nonempty E] : Nonempty (WithCStarModule E) := ‹Nonempty E›
instance instUnique [Unique E] : Unique (WithCStarModule E) := ‹Unique E›
instance instAddCommGroup [AddCommGroup E] : AddCommGroup (WithCStarModule E) := ‹AddCommGroup E›
instance instSMul {R : Type*} [SMul R E] : SMul R (WithCStarModule E) := ‹SMul R E›
instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R (WithCStarModule E) :=
  ‹Module R E›
instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' (WithCStarModule E) :=
  ‹IsScalarTower R R' E›
instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' (WithCStarModule E) :=
  ‹SMulCommClass R R' E›
instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R (WithCStarModule E) :=
  ‹Module.Finite R E›
section Equiv
variable {R E}
variable [SMul R E] (c : R) (x y : WithCStarModule E) (x' y' : E)
section AddCommGroup
variable [AddCommGroup E]
@[simp]
theorem equiv_zero : equiv E 0 = 0 :=
  rfl
@[simp]
theorem equiv_symm_zero : (equiv E).symm 0 = 0 :=
  rfl
@[simp]
theorem equiv_add : equiv E (x + y) = equiv E x + equiv E y :=
  rfl
@[simp]
theorem equiv_symm_add :
    (equiv E).symm (x' + y') = (equiv E).symm x' + (equiv E).symm y' :=
  rfl
@[simp]
theorem equiv_sub : equiv E (x - y) = equiv E x - equiv E y :=
  rfl
@[simp]
theorem equiv_symm_sub :
    (equiv E).symm (x' - y') = (equiv E).symm x' - (equiv E).symm y' :=
  rfl
@[simp]
theorem equiv_neg : equiv E (-x) = -equiv E x :=
  rfl
@[simp]
theorem equiv_symm_neg : (equiv E).symm (-x') = -(equiv E).symm x' :=
  rfl
end AddCommGroup
@[simp]
theorem equiv_smul : equiv E (c • x) = c • equiv E x :=
  rfl
@[simp]
theorem equiv_symm_smul : (equiv E).symm (c • x') = c • (equiv E).symm x' :=
  rfl
end Equiv
@[simps (config := .asFn)]
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ E ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _
    invFun := (equiv _).symm }
variable {E}
instance [u : UniformSpace E] : UniformSpace (C⋆ᵐᵒᵈ E) := u.comap <| equiv E
instance [Bornology E] : Bornology (C⋆ᵐᵒᵈ E) := Bornology.induced <| equiv E
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ E ≃ᵤ E :=
  equiv E |>.toUniformEquivOfIsUniformInducing ⟨rfl⟩
instance [UniformSpace E] [CompleteSpace E] : CompleteSpace (C⋆ᵐᵒᵈ E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance
end Basic
section Prod
variable {R E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ (E × F)) (c : R)
section AddCommGroup
variable [AddCommGroup E] [AddCommGroup F]
@[simp]
theorem zero_fst : (0 : C⋆ᵐᵒᵈ (E × F)).fst = 0 :=
  rfl
@[simp]
theorem zero_snd : (0 : C⋆ᵐᵒᵈ (E × F)).snd = 0 :=
  rfl
@[simp]
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl
@[simp]
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl
@[simp]
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl
@[simp]
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl
@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl
@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl
end AddCommGroup
@[simp]
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl
@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl
@[simp]
theorem equiv_fst (x : C⋆ᵐᵒᵈ (E × F)) : (equiv (E × F) x).fst = x.fst :=
  rfl
@[simp]
theorem equiv_snd (x : C⋆ᵐᵒᵈ (E × F)) : (equiv (E × F) x).snd = x.snd :=
  rfl
@[simp]
theorem equiv_symm_fst (x : E × F) : ((equiv (E × F)).symm x).fst = x.fst :=
  rfl
@[simp]
theorem equiv_symm_snd (x : E × F) : ((equiv (E × F)).symm x).snd = x.snd :=
  rfl
end Prod
section Pi
instance {ι : Type*} (E : ι → Type*) : CoeFun (C⋆ᵐᵒᵈ (Π i, E i)) (fun _ ↦ Π i, E i) where
  coe := WithCStarModule.equiv _
@[ext]
protected theorem ext {ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ (Π i, E i)}
    (h : ∀ i, x i = y i) : x = y :=
  funext h
variable {R ι : Type*} {E : ι → Type*}
variable [∀ i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ (Π i, E i)) (i : ι)
section AddCommGroup
variable [∀ i, AddCommGroup (E i)]
@[simp]
theorem zero_apply : (0 : C⋆ᵐᵒᵈ (Π i, E i)) i = 0 :=
  rfl
@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl
@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl
@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl
end AddCommGroup
@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl
@[simp]
theorem equiv_pi_apply (i : ι) : equiv _ x i = x i :=
  rfl
@[simp]
theorem equiv_symm_pi_apply (x : ∀ i, E i) (i : ι) :
    (WithCStarModule.equiv _).symm x i = x i :=
  rfl
end Pi
end WithCStarModule