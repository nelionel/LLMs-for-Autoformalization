import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
open EquivLike
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom
class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] extends StarHomClass F A B : Prop
namespace NonUnitalStarRingHomClass
variable {F A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B]
@[coe]
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A →⋆ₙ+* B :=
  { (f : A →ₙ+* B) with
    map_star' := map_star f }
instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A →⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩
end NonUnitalStarRingHomClass
namespace NonUnitalStarRingHom
section Basic
variable {A B C D : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]
variable [NonUnitalNonAssocSemiring D] [Star D]
instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩,  _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B where
  map_star f := f.map_star'
def Simps.apply (f : A →⋆ₙ+* B) : A → B := f
initialize_simps_projections NonUnitalStarRingHom (toFun → apply)
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    [NonUnitalStarRingHomClass F A B] (f : F) : ⇑(f : A →⋆ₙ+* B) = f :=
  rfl
@[simp]
theorem coe_toNonUnitalRingHom (f : A →⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f :=
  rfl
@[ext]
theorem ext {f g : A →⋆ₙ+* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
protected def copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : A →⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f
@[simp]
theorem coe_copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
@[simp]
theorem coe_mk (f : A →ₙ+* B) (h) :
    ((⟨f, h⟩ : A  →⋆ₙ+* B) : A → B) = f :=
  rfl
@[simp]
theorem mk_coe (f : A →⋆ₙ+* B) (h₁ h₂ h₃ h₄) :
    (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →⋆ₙ+* B) = f := by
  ext
  rfl
section
variable (A)
protected def id : A →⋆ₙ+* A :=
  { (1 : A →ₙ+* A) with map_star' := fun _ => rfl }
@[simp]
theorem coe_id : ⇑(NonUnitalStarRingHom.id A) = id :=
  rfl
end
def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [Function.comp_def, map_star, map_star] }
@[simp]
theorem coe_comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : ⇑(comp f g) = f ∘ g :=
  rfl
@[simp]
theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
  rfl
@[simp]
theorem comp_assoc (f : C →⋆ₙ+* D) (g : B →⋆ₙ+* C) (h : A →⋆ₙ+* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
@[simp]
theorem id_comp (f : A →⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f :=
  ext fun _ => rfl
@[simp]
theorem comp_id (f : A →⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f :=
  ext fun _ => rfl
instance : Monoid (A →⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id
@[simp]
theorem coe_one : ((1 : A →⋆ₙ+* A) : A → A) = id :=
  rfl
theorem one_apply (a : A) : (1 : A →⋆ₙ+* A) a = a :=
  rfl
end Basic
section Zero
variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]
instance : Zero (A →⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩
instance : Inhabited (A →⋆ₙ+* B) :=
  ⟨0⟩
instance : MonoidWithZero (A →⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f
@[simp]
theorem coe_zero : ((0 : A →⋆ₙ+* B) : A → B) = 0 :=
  rfl
theorem zero_apply (a : A) : (0 : A →⋆ₙ+* B) a = 0 :=
  rfl
end Zero
end NonUnitalStarRingHom
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B
add_decl_doc StarRingEquiv.toRingEquiv
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B]
    extends RingEquivClass F A B : Prop where
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)
namespace StarRingEquivClass
instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B :=
  { hF with }
instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [RingEquivClass F A B]
    [StarRingEquivClass F A B] : NonUnitalStarRingHomClass F A B :=
  { }
@[coe]
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (f : A ≃+* B) with
    map_star' := map_star f}
instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩
end StarRingEquivClass
namespace StarRingEquiv
section Basic
variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]
instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr
instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'
instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective
@[simp]
theorem toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e :=
  rfl
@[ext]
theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h
@[refl]
def refl : A ≃⋆+* A :=
  { RingEquiv.refl A with
    map_star' := fun _ => rfl }
instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩
@[simp]
theorem coe_refl : ⇑(refl : A ≃⋆+* A) = id :=
  rfl
@[symm]
nonrec def symm (e : A ≃⋆+* B) : B ≃⋆+* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm }
def Simps.apply (e : A ≃⋆+* B) : A → B := e
def Simps.symm_apply (e : A ≃⋆+* B) : B → A :=
  e.symm
initialize_simps_projections StarRingEquiv (toFun → apply, invFun → symm_apply)
@[simp]
theorem invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm :=
  rfl
@[simp]
theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) → B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e := rfl
@[simp]
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅) :=
  (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm
@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl
@[simp]
theorem refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl :=
  rfl
@[trans]
def trans (e₁ : A≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }
@[simp]
theorem apply_symm_apply (e : A ≃⋆+* B) : ∀ x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply
@[simp]
theorem symm_apply_apply (e : A ≃⋆+* B) : ∀ x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply
@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl
@[simp]
theorem coe_trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
@[simp]
theorem trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e :=
  e.left_inv
theorem rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e :=
  e.right_inv
end Basic
section Bijective
variable {F G A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]
variable [FunLike G B A]
@[simps]
def ofStarRingHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆+* B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }
@[simp]
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarRingEquiv.ofBijective f hf : A → B) = f :=
  rfl
theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarRingEquiv.ofBijective f hf) a = f a :=
  rfl
end Bijective
end StarRingEquiv