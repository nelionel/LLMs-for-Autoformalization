import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
universe u u₁ v w w₁ w₂ w₃
variable {R : Type u} {S : Type u₁}
structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B
@[inherit_doc NonUnitalAlgHom]
infixr:25 " →ₙₐ " => NonUnitalAlgHom _
@[inherit_doc]
notation:25 A " →ₛₙₐ[" φ "] " B => NonUnitalAlgHom φ A B
@[inherit_doc]
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom (MonoidHom.id R) A B
attribute [nolint docBlame] NonUnitalAlgHom.toMulHom
class NonUnitalAlgSemiHomClass (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
    (φ : outParam (R →* S)) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction S B] [FunLike F A B]
    extends DistribMulActionSemiHomClass F φ A B, MulHomClass F A B : Prop
abbrev NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*)
    [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] :=
  NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B
namespace NonUnitalAlgHomClass
instance (priority := 100) toNonUnitalRingHomClass
  {F R S A B : Type*} {_ : Monoid R} {_ : Monoid S} {φ : outParam (R →* S)}
    {_ : NonUnitalNonAssocSemiring A} [DistribMulAction R A]
    {_ : NonUnitalNonAssocSemiring B} [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with }
variable [Semiring R] [Semiring S] {φ : R →+* S}
  {A B : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module S B]
instance (priority := 100) {F R S A B : Type*}
    {_ : Semiring R} {_ : Semiring S} {φ : R →+* S}
    {_ : NonUnitalSemiring A} {_ : NonUnitalSemiring B} [Module R A] [Module S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass (R := R) (S := S) F φ A B] :
    SemilinearMapClass F φ A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with map_smulₛₗ := map_smulₛₗ }
instance (priority := 100) {F : Type*} [FunLike F A B] [Module R B] [NonUnitalAlgHomClass F R A B] :
    LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smulₛₗ }
@[coe]
def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R →* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A →ₛₙₐ[φ] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }
instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A →ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    toFun := f
    map_smul' := map_smulₛₗ f }
instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩
end NonUnitalAlgHomClass
namespace NonUnitalAlgHom
variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]
instance : DFunLike (A →ₛₙₐ[φ] B) A fun _ => B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
@[simp]
theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f :=
  rfl
def Simps.apply (f : A →ₛₙₐ[φ] B) : A → B := f
initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)
variable {φ A B C}
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f :=
  rfl
theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
instance : FunLike (A →ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' := coe_injective
instance : NonUnitalAlgSemiHomClass (A →ₛₙₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'
@[ext]
theorem ext {f g : A →ₛₙₐ[φ] B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
theorem congr_fun {f g : A →ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl
@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f :=
  rfl
@[simp]
theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  rfl
@[simp]
theorem toDistribMulActionHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toDistribMulActionHom = ↑f :=
  rfl
@[simp]
theorem toMulHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toMulHom = ↑f :=
  rfl
@[simp, norm_cast]
theorem coe_to_distribMulActionHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₑ+[φ] B) = f :=
  rfl
@[simp, norm_cast]
theorem coe_to_mulHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₙ* B) = f :=
  rfl
theorem to_distribMulActionHom_injective {f g : A →ₛₙₐ[φ] B}
    (h : (f : A →ₑ+[φ] B) = (g : A →ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a
theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a
@[norm_cast]
theorem coe_distribMulActionHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  rfl
@[norm_cast]
theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  rfl
@[simp] 
protected theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x :=
  map_smulₛₗ _ _ _
protected theorem map_add (f : A →ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _
protected theorem map_mul (f : A →ₛₙₐ[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _
protected theorem map_zero (f : A →ₛₙₐ[φ] B) : f 0 = 0 :=
  map_zero _
protected def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }
@[simp]
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl
instance : Zero (A →ₛₙₐ[φ] B) :=
  ⟨{ (0 : A →ₑ+[φ] B) with map_mul' := by simp }⟩
instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩
@[simp]
theorem coe_zero : ⇑(0 : A →ₛₙₐ[φ] B) = 0 :=
  rfl
@[simp]
theorem coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id :=
  rfl
theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 :=
  rfl
theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
  rfl
instance : Inhabited (A →ₛₙₐ[φ] B) :=
  ⟨0⟩
variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}
set_option linter.unusedVariables false in
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →ₑ+[ψ] C).comp (g : A →ₑ+[φ] B) with }
@[simp, norm_cast]
theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := rfl
theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := rfl
variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]
def inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →ₙₐ[R] A :=
  { (f : A →ₙ* B₁).inverse g h₁ h₂, (f : A →+[R] B₁).inverse g h₁ h₂ with }
@[simp]
theorem coe_inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ → A) = g :=
  rfl
def inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₛₙₐ[φ'] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero, h₁]
    map_add' := fun x y ↦ by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x, ← h₂ y, ← map_add, h₁, h₂, h₂] }
@[simp]
theorem coe_inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B → A) = g :=
  rfl
section Prod
variable (R A B)
variable  [DistribMulAction R B]
@[simps]
def fst : A × B →ₙₐ[R] A where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
@[simps]
def snd : A × B →ₙₐ[R] B where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
variable {R A B}
variable [DistribMulAction R C]
@[simps]
def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C where
  toFun := Pi.prod f g
  map_zero' := by simp only [Pi.prod, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Pi.prod, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Pi.prod, map_smul, MonoidHom.id_apply, id_eq, Prod.smul_mk]
theorem coe_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
@[simp]
theorem fst_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  rfl
@[simp]
theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl
@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  coe_injective Pi.prod_fst_snd
@[simps]
def prodEquiv : (A →ₙₐ[R] B) × (A →ₙₐ[R] C) ≃ (A →ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv _ := rfl
  right_inv _ := rfl
variable (R A B)
def inl : A →ₙₐ[R] A × B :=
  prod 1 0
def inr : B →ₙₐ[R] A × B :=
  prod 0 1
variable {R A B}
@[simp]
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl
theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl
@[simp]
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl
theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl
end Prod
end NonUnitalAlgHom
namespace AlgHom
variable {F R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]
instance (priority := 100) [FunLike F A B] [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smulₛₗ := map_smul }
@[coe]
def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := map_smul f }
instance NonUnitalAlgHom.hasCoe : CoeOut (A →ₐ[R] B) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩
@[simp]
theorem toNonUnitalAlgHom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl
end AlgHom
section RestrictScalars
namespace NonUnitalAlgHom
variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]
def restrictScalars (f : A →ₙₐ[S] B) : A →ₙₐ[R] B :=
  { (f : A →ₙ+* B) with
    map_smul' := fun r x ↦ by have := map_smul f (r • 1) x; simpa }
@[simp]
lemma restrictScalars_apply (f : A →ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
lemma coe_restrictScalars (f : A →ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl
lemma coe_restrictScalars' (f : A →ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₙₐ[S] B) → A →ₙₐ[R] B) :=
  fun _ _ h ↦ ext (congr_fun h : _)
end NonUnitalAlgHom
end RestrictScalars