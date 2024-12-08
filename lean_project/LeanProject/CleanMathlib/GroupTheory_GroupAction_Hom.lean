import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Hom.CompTypeclasses
assert_not_exists Submonoid
section MulActionHom
variable {M' : Type*}
variable {M : Type*} {N : Type*} {P : Type*}
variable (φ : M → N) (ψ : N → P) (χ : M → P)
variable (X : Type*) [SMul M X] [SMul M' X]
variable (Y : Type*) [SMul N Y] [SMul M' Y]
variable (Z : Type*) [SMul P Z]
structure AddActionHom {M N : Type*} (φ: M → N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  protected toFun : X → Y
  protected map_vadd' : ∀ (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x
@[to_additive]
structure MulActionHom where
  protected toFun : X → Y
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y
notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y
notation:25 (name := «AddActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y
notation:25 (name := «AddActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => AddActionHom (@id M) X Y
class AddActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [VAdd M X] [VAdd N Y] [FunLike F X Y] : Prop where
  map_vaddₛₗ : ∀ (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)
@[to_additive]
class MulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)
export MulActionSemiHomClass (map_smulₛₗ)
export AddActionSemiHomClass (map_vaddₛₗ)
@[to_additive "`MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`."]
abbrev MulActionHomClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [SMul M X] [SMul M Y] [FunLike F X Y] :=
  MulActionSemiHomClass F (@id M) X Y
@[to_additive] instance : FunLike (MulActionHom φ X Y) X Y where
  coe := MulActionHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
@[to_additive (attr := simp)]
theorem map_smul {F M X Y : Type*} [SMul M X] [SMul M Y]
    [FunLike F X Y] [MulActionHomClass F M X Y]
    (f : F) (c : M) (x : X) : f (c • x) = c • f x :=
  map_smulₛₗ f c x
@[to_additive]
instance : MulActionSemiHomClass (X →ₑ[φ] Y) φ X Y where
  map_smulₛₗ := MulActionHom.map_smul'
initialize_simps_projections MulActionHom (toFun → apply)
initialize_simps_projections AddActionHom (toFun → apply)
namespace MulActionHom
variable {φ X Y}
variable {F : Type*} [FunLike F X Y]
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `AddActionSemiHomClass F φ X Y`
  into an actual `AddActionHom`.
  This is declared as the default coercion from `F` to `AddActionSemiHom φ X Y`."]
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X →ₑ[φ] Y where
  toFun := DFunLike.coe f
  map_smul' := map_smulₛₗ f
@[to_additive]
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X →ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩
variable (M' X Y F) in
@[to_additive]
theorem _root_.IsScalarTower.smulHomClass [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
    [MulActionHomClass F X X Y] : MulActionHomClass F M' X Y where
  map_smulₛₗ f m x := by
    rw [← mul_one (m • x), ← smul_eq_mul, map_smul, smul_assoc, ← map_smul,
      smul_eq_mul, mul_one, id_eq]
@[to_additive]
protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul f m x
@[to_additive (attr := ext)]
theorem ext {f g : X →ₑ[φ] Y} :
    (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g
@[to_additive]
protected theorem congr_fun {f g : X →ₑ[φ] Y} (h : f = g) (x : X) :
    f x = g x :=
  DFunLike.congr_fun h _
@[to_additive "Two equal maps on scalars give rise to an equivariant map for identity"]
def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a
@[to_additive (attr := simp)]
theorem ofEq_coe {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) :
    (f.ofEq h).toFun = f.toFun := rfl
@[to_additive (attr := simp)]
theorem ofEq_apply {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) (a : X) :
    (f.ofEq h) a = f a :=
  rfl
variable {ψ χ} (M N)
@[to_additive "The identity map as an equivariant map."]
protected def id : X →[M] X :=
  ⟨id, fun _ _ => rfl⟩
variable {M N Z}
@[to_additive (attr := simp)]
theorem id_apply (x : X) :
    MulActionHom.id M x = x :=
  rfl
end MulActionHom
namespace MulActionHom
open MulActionHom
variable {φ ψ χ X Y Z}
@[to_additive "Composition of two equivariant maps."]
def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
    X →ₑ[χ] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩
@[to_additive (attr := simp)]
theorem comp_apply
    (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [CompTriple φ ψ χ] (x : X) :
    g.comp f x = g (f x) := rfl
@[to_additive (attr := simp)]
theorem id_comp (f : X →ₑ[φ] Y) :
    (MulActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[to_additive (attr := simp)]
theorem comp_id (f : X →ₑ[φ] Y) :
    f.comp (MulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[to_additive (attr := simp)]
theorem comp_assoc {Q T : Type*} [SMul Q T]
    {η : P → Q} {θ : M → Q} {ζ : N → Q}
    (h : Z →ₑ[η] T) (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y)
    [CompTriple φ ψ χ] [CompTriple χ η θ]
    [CompTriple ψ η ζ] [CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl
variable {φ' : N → M}
variable {Y₁ : Type*} [SMul M Y₁]
@[to_additive (attr := simps) "The inverse of a bijective equivariant map is equivariant."]
def inverse (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ →[M] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul, id_eq]
      _ = m • g x := by rw [h₁]
@[to_additive (attr := simps) "The inverse of a bijective equivariant map is equivariant."]
def inverse' (f : X →ₑ[φ] Y) (g : Y → X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    Y →ₑ[φ'] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]
@[to_additive]
lemma inverse_eq_inverse' (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
  inverse f g h₁ h₂ =  inverse' f g (congrFun rfl) h₁ h₂ := by
  rfl
@[to_additive]
theorem inverse'_inverse'
    {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    inverse' (inverse' f g k₂ h₁ h₂) f k₁ h₂ h₁ = f :=
  ext fun _ => rfl
@[to_additive]
theorem comp_inverse' {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (inverse' f g k₂ h₁ h₂).comp f (κ := CompTriple.comp_inv k₁)
      = MulActionHom.id M := by
  rw [MulActionHom.ext_iff]
  intro x
  simp only [comp_apply, inverse_apply, id_apply]
  exact h₁ x
@[to_additive]
theorem inverse'_comp {f : X →ₑ[φ] Y} {g : Y → X}
    {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (inverse' f g k₂ h₁ h₂) (κ := CompTriple.comp_inv k₂) = MulActionHom.id N := by
  rw [MulActionHom.ext_iff]
  intro x
  simp only [comp_apply, inverse_apply, id_apply]
  exact h₂ x
@[to_additive (attr := simps) "If additive actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-additive action homomorphism."]
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _
end MulActionHom
end MulActionHom
section DistribMulAction
variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable {P : Type*} [Monoid P]
variable (φ : M →* N) (φ' : N →* M) (ψ : N →* P) (χ : M →* P)
variable (A : Type*) [AddMonoid A] [DistribMulAction M A]
variable (B : Type*) [AddMonoid B] [DistribMulAction N B]
variable (B₁ : Type*) [AddMonoid B₁] [DistribMulAction M B₁]
variable (C : Type*) [AddMonoid C] [DistribMulAction P C]
variable (A' : Type*) [AddGroup A'] [DistribMulAction M A']
variable (B' : Type*) [AddGroup B'] [DistribMulAction N B']
structure DistribMulActionHom extends A →ₑ[φ] B, A →+ B
add_decl_doc DistribMulActionHom.toAddMonoidHom
add_decl_doc DistribMulActionHom.toMulActionHom
@[inherit_doc]
notation:25 (name := «DistribMulActionHomLocal≺»)
  A " →ₑ+[" φ:25 "] " B:0 => DistribMulActionHom φ A B
@[inherit_doc]
notation:25 (name := «DistribMulActionHomIdLocal≺»)
  A " →+[" M:25 "] " B:0 => DistribMulActionHom (MonoidHom.id M) A B
class DistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (A B : outParam Type*)
    [Monoid M] [Monoid N]
    [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
    [FunLike F A B]
    extends MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B : Prop
abbrev DistribMulActionHomClass (F : Type*) (M : outParam Type*)
    (A B : outParam Type*) [Monoid M] [AddMonoid A] [AddMonoid B]
    [DistribMulAction M A] [DistribMulAction M B] [FunLike F A B] :=
    DistribMulActionSemiHomClass F (MonoidHom.id M) A B
namespace DistribMulActionHom
instance : FunLike (A →ₑ+[φ] B) A B where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr
instance : DistribMulActionSemiHomClass (A →ₑ+[φ] B) φ A B where
  map_smulₛₗ m := m.map_smul'
  map_zero := DistribMulActionHom.map_zero'
  map_add := DistribMulActionHom.map_add'
variable {φ φ' A B B₁}
variable {F : Type*} [FunLike F A B]
@[coe]
def _root_.DistribMulActionSemiHomClass.toDistribMulActionHom
    [DistribMulActionSemiHomClass F φ A B]
    (f : F) : A →ₑ+[φ] B :=
  { (f : A →+ B),  (f : A →ₑ[φ] B) with }
instance [DistribMulActionSemiHomClass F φ A B] :
  CoeTC F (A →ₑ+[φ] B) :=
  ⟨DistribMulActionSemiHomClass.toDistribMulActionHom⟩
@[simps]
def _root_.SMulCommClass.toDistribMulActionHom {M} (N A : Type*) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }
@[simp]
theorem toFun_eq_coe (f : A →ₑ+[φ] B) : f.toFun = f := rfl
@[norm_cast]
theorem coe_fn_coe (f : A →ₑ+[φ] B) : ⇑(f : A →+ B) = f :=
  rfl
@[norm_cast]
theorem coe_fn_coe' (f : A →ₑ+[φ] B) : ⇑(f : A →ₑ[φ] B) = f :=
  rfl
@[ext]
theorem ext {f g : A →ₑ+[φ] B} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g
protected theorem congr_fun {f g : A →ₑ+[φ] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h _
theorem toMulActionHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →ₑ[φ] B) = (g : A →ₑ[φ] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a
theorem toAddMonoidHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a
protected theorem map_zero (f : A →ₑ+[φ] B) : f 0 = 0 :=
  map_zero f
protected theorem map_add (f : A →ₑ+[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add f x y
protected theorem map_neg (f : A' →ₑ+[φ] B') (x : A') : f (-x) = -f x :=
  map_neg f x
protected theorem map_sub (f : A' →ₑ+[φ] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub f x y
protected theorem map_smulₑ (f : A →ₑ+[φ] B) (m : M) (x : A) : f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x
variable (M)
protected def id : A →+[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩
@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x := by
  rfl
variable {M C ψ χ}
instance : Zero (A →ₑ+[φ] B) :=
  ⟨{ (0 : A →+ B) with map_smul' := fun m _ => by change (0 : B) = (φ m) • (0 : B); rw [smul_zero]}⟩
instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩
@[simp]
theorem coe_zero : ⇑(0 : A →ₑ+[φ] B) = 0 :=
  rfl
@[simp]
theorem coe_one : ⇑(1 : A →+[M] A) = id :=
  rfl
theorem zero_apply (a : A) : (0 : A →ₑ+[φ] B) a = 0 :=
  rfl
theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl
instance : Inhabited (A →ₑ+[φ] B) :=
  ⟨0⟩
set_option linter.unusedVariables false in
def comp (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₑ+[χ] C :=
  { MulActionHom.comp (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B),
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }
@[simp]
theorem comp_apply
    (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) : g.comp f x = g (f x) :=
  rfl
@[simp]
theorem id_comp (f : A →ₑ+[φ] B) : comp (DistribMulActionHom.id N) f = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[simp]
theorem comp_id (f : A →ₑ+[φ] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[simp]
theorem comp_assoc {Q D : Type*} [Monoid Q] [AddMonoid D] [DistribMulAction Q D]
    {η : P →* Q} {θ : M →* Q} {ζ : N →* Q}
    (h : C →ₑ+[η] D) (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B)
    [MonoidHom.CompTriple φ ψ χ] [MonoidHom.CompTriple χ η θ]
    [MonoidHom.CompTriple ψ η ζ] [MonoidHom.CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl
@[simps]
def inverse (f : A →+[M] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →+[M] A :=
  { (f : A →+ B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }
section Semiring
variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (T : Type*) [Semiring T] [MulSemiringAction P T]
variable {R S N'}
variable [AddMonoid N'] [DistribMulAction S N']
variable {σ : R →* S}
@[ext]
theorem ext_ring {f g : R →ₑ+[σ] N'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x, ← smul_eq_mul R, f.map_smulₑ, g.map_smulₑ, h]
end Semiring
end DistribMulActionHom
variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (R' : Type*) [Ring R'] [MulSemiringAction M R']
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (S' : Type*) [Ring S'] [MulSemiringAction N S']
variable (T : Type*) [Semiring T] [MulSemiringAction P T]
structure MulSemiringActionHom extends R →ₑ+[φ] S, R →+* S
abbrev MulSemiringActionHom
  (M : Type*) [Monoid M]
  (R : Type*) [Semiring R] [MulSemiringAction M R]
  (S : Type*) [Semiring S] [MulSemiringAction M S]:= MulSemiringActionHom (MonoidHom.id M) R S
-/
add_decl_doc MulSemiringActionHom.toRingHom
add_decl_doc MulSemiringActionHom.toDistribMulActionHom
@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S
@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam Type*} [Monoid M] [Monoid N]
    (φ : outParam (M → N))
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S]
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S : Prop
abbrev MulSemiringActionHomClass
    (F : Type*)
    {M : outParam Type*} [Monoid M]
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] [FunLike F R S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S
namespace MulSemiringActionHom
instance : FunLike (R →ₑ+*[φ] S) R S where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr
instance : MulSemiringActionSemiHomClass (R →ₑ+*[φ] S) φ R S where
  map_zero m := m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'
  map_smulₛₗ m := m.map_smul'
variable {φ R S}
variable {F : Type*} [FunLike F R S]
@[coe]
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S]
    (f : F) : R →ₑ+*[φ] S :=
 { (f : R →+* S),  (f : R →ₑ+[φ] S) with }
instance [MulSemiringActionSemiHomClass F φ R S] :
    CoeTC F (R →ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩
@[norm_cast]
theorem coe_fn_coe (f : R →ₑ+*[φ] S) : ⇑(f : R →+* S) = f :=
  rfl
@[norm_cast]
theorem coe_fn_coe' (f : R →ₑ+*[φ] S) : ⇑(f : R →ₑ+[φ] S) = f :=
  rfl
@[ext]
theorem ext {f g : R →ₑ+*[φ] S} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g
protected theorem map_zero (f : R →ₑ+*[φ] S) : f 0 = 0 :=
  map_zero f
protected theorem map_add (f : R →ₑ+*[φ] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y
protected theorem map_neg (f : R' →ₑ+*[φ] S') (x : R') : f (-x) = -f x :=
  map_neg f x
protected theorem map_sub (f : R' →ₑ+*[φ] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y
protected theorem map_one (f : R →ₑ+*[φ] S) : f 1 = 1 :=
  map_one f
protected theorem map_mul (f : R →ₑ+*[φ] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y
protected theorem map_smulₛₗ (f : R →ₑ+*[φ] S) (m : M) (x : R) : f (m • x) = φ m • f x :=
  map_smulₛₗ f m x
protected theorem map_smul [MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R) :
    f (m • x) = m • f x :=
  map_smulₛₗ f m x
end MulSemiringActionHom
namespace MulSemiringActionHom
variable (M) {R}
protected def id : R →+*[M] R :=
  ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩
@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl
end MulSemiringActionHom
namespace MulSemiringActionHom
open MulSemiringActionHom
variable {R S T}
variable {φ φ' ψ χ}
set_option linter.unusedVariables false in
def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R →ₑ+*[χ] T :=
  { DistribMulActionHom.comp (g : S →ₑ+[ψ] T) (f : R →ₑ+[φ] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }
@[simp]
theorem comp_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
    g.comp f x = g (f x) := rfl
@[simp]
theorem id_comp (f : R →ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[simp]
theorem comp_id (f : R →ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
@[simps]
def inverse' (f : R →ₑ+*[φ] S) (g : S → R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S →ₑ+*[φ'] R :=
  { (f : R →+ S).inverse g h₁ h₂,
    (f : R →* S).inverse g h₁ h₂,
    (f : R →ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }
@[simps]
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R →+*[M] S₁) (g : S₁ → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S₁ →+*[M] R :=
  { (f : R →+ S₁).inverse g h₁ h₂,
    (f : R →* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }
end MulSemiringActionHom
end DistribMulAction