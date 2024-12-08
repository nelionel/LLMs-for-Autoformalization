import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Logic.Equiv.Basic
open Function
variable {F α β M N P G H : Type*}
namespace EmbeddingLike
variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]
@[to_additive (attr := simp)]
theorem map_eq_one_iff {f : F} {x : M} :
    f x = 1 ↔ x = 1 :=
  _root_.map_eq_one_iff f (EmbeddingLike.injective f)
@[to_additive]
theorem map_ne_one_iff {f : F} {x : M} :
    f x ≠ 1 ↔ x ≠ 1 :=
  map_eq_one_iff.not
end EmbeddingLike
structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B
class AddEquivClass (F : Type*) (A B : outParam Type*) [Add A] [Add B] [EquivLike F A B] :
    Prop where
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b
add_decl_doc AddEquiv.toEquiv
add_decl_doc AddEquiv.toAddHom
@[to_additive]
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N
attribute [to_additive existing] MulEquiv.toMulHom
add_decl_doc MulEquiv.toEquiv
add_decl_doc MulEquiv.toMulHom
infixl:25 " ≃* " => MulEquiv
infixl:25 " ≃+ " => AddEquiv
@[to_additive]
lemma MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] :
    Function.Injective (toEquiv : (α ≃* β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
@[to_additive]
class MulEquivClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [EquivLike F A B] :
    Prop where
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b
@[to_additive]
alias MulEquivClass.map_eq_one_iff := EmbeddingLike.map_eq_one_iff
attribute [deprecated EmbeddingLike.map_eq_one_iff (since := "2024-11-10")]
MulEquivClass.map_eq_one_iff
attribute [deprecated EmbeddingLike.map_eq_zero_iff (since := "2024-11-10")]
AddEquivClass.map_eq_zero_iff
@[to_additive]
alias MulEquivClass.map_ne_one_iff := EmbeddingLike.map_ne_one_iff
attribute [deprecated EmbeddingLike.map_ne_one_iff (since := "2024-11-10")]
MulEquivClass.map_ne_one_iff
attribute [deprecated EmbeddingLike.map_ne_zero_iff (since := "2024-11-10")]
AddEquivClass.map_ne_zero_iff
namespace MulEquivClass
variable (F)
variable [EquivLike F M N]
@[to_additive]
instance (priority := 100) instMulHomClass (F : Type*)
    [Mul M] [Mul N] [EquivLike F M N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with }
@[to_additive]
instance (priority := 100) instMonoidHomClass
    [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (EquivLike.inv e (1 : N) : M) :=
          congr_arg _ (EquivLike.right_inv e 1).symm
        _ = e (EquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := EquivLike.right_inv e 1 }
end MulEquivClass
variable [EquivLike F α β]
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `AddEquivClass F α β` into an actual
`AddEquiv`. This is declared as the default coercion from `F` to `α ≃+ β`."]
def MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α ≃* β :=
  { (f : α ≃ β), (f : α →ₙ* β) with }
@[to_additive "Any type satisfying `AddEquivClass` can be cast into `AddEquiv` via
`AddEquivClass.toAddEquiv`. "]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨MulEquivClass.toMulEquiv⟩
@[to_additive]
theorem MulEquivClass.toMulEquiv_injective [Mul α] [Mul β] [MulEquivClass F α β] :
    Function.Injective ((↑) : F → α ≃* β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃* β ↦ e.toFun a) e
namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]
section coe
@[to_additive]
instance : EquivLike (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁
@[to_additive] 
instance : CoeFun (M ≃* N) fun _ ↦ M → N where
  coe f := f
@[to_additive]
instance : MulEquivClass (M ≃* N) M N where
  map_mul f := f.map_mul'
@[to_additive (attr := ext)
  "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x
@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (mk f hf : M → N) = f := rfl
@[to_additive (attr := simp)]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl
@[to_additive (attr := simp)]
theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl
@[to_additive (attr := simp)]
theorem toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f :=
  rfl
@[to_additive (attr := simp)]
theorem coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f := rfl
@[to_additive (attr := simp 1100)]
theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M → N) = f := rfl
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩
end coe
section map
@[to_additive "An additive isomorphism preserves addition."]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  map_mul f
attribute [deprecated map_mul (since := "2024-08-08")] MulEquiv.map_mul
attribute [deprecated map_add (since := "2024-08-08")] AddEquiv.map_add
end map
section bijective
@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e
@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e
@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e
@[to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff
end bijective
section refl
@[to_additive (attr := refl) "The identity map is an additive isomorphism."]
def refl (M : Type*) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }
@[to_additive]
instance : Inhabited (M ≃* M) := ⟨refl M⟩
@[to_additive (attr := simp)]
theorem coe_refl : ↑(refl M) = id := rfl
@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl
end refl
section symm
@[to_additive]
lemma symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) :
    h.symm (x * y) = h.symm x * h.symm y :=
  map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y
@[to_additive (attr := symm) "The inverse of an isomorphism is an isomorphism."]
def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, h.symm_map_mul⟩
@[to_additive] 
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl
@[to_additive (attr := simp)]
theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N → M) = f.symm := rfl
@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm := rfl
@[to_additive (attr := simp)]
theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl
@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl
@[to_additive]
theorem symm_bijective : Function.Bijective (symm : (M ≃* N) → N ≃* M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
@[to_additive (attr := simp)]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
@[to_additive (attr := simp)]
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm_map_mul⟩ := rfl
@[to_additive (attr := simp)]
theorem refl_symm : (refl M).symm = refl M := rfl
@[to_additive (attr := simp) "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y
@[to_additive (attr := simp) "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply
@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply
@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g
@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g
@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g
@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g
@[to_additive (attr := simp)]
theorem _root_.MulEquivClass.apply_coe_symm_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : β) :
    e ((e : α ≃* β).symm x) = x :=
  (e : α ≃* β).right_inv x
@[to_additive (attr := simp)]
theorem _root_.MulEquivClass.coe_symm_apply_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : α) :
    (e : α ≃* β).symm (e x) = x :=
  (e : α ≃* β).left_inv x
end symm
section simps
@[to_additive "See Note [custom simps projection]"] 
def Simps.symm_apply (e : M ≃* N) : N → M :=
  e.symm
initialize_simps_projections AddEquiv (toFun → apply, invFun → symm_apply)
initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)
end simps
section trans
@[to_additive (attr := trans) "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul, map_mul] }
@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl
@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl
@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl
@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply
@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply
end trans
section unique
@[to_additive "The `AddEquiv` between two `AddMonoid`s with a unique element."]
def mulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.equivOfUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with
  a unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := mulEquivOfUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _
end unique
end Mul
section MulOneClass
variable [MulOneClass M] [MulOneClass N] [MulOneClass P]
@[to_additive]
theorem coe_monoidHom_refl : (refl M : M →* M) = MonoidHom.id M := rfl
@[to_additive]
lemma coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ := rfl
@[to_additive (attr := simp)]
lemma coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) :
    (e : M →* N).comp e.symm = MonoidHom.id _ := by ext; simp
@[to_additive (attr := simp)]
lemma coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) :
    (e.symm : N →* M).comp e = MonoidHom.id _ := by ext; simp
@[to_additive]
lemma comp_left_injective (e : M ≃* N) : Injective fun f : N →* P ↦ f.comp (e : M →* N) :=
  LeftInverse.injective (g := fun f ↦ f.comp e.symm) fun f ↦ by simp [MonoidHom.comp_assoc]
@[to_additive]
lemma comp_right_injective (e : M ≃* N) : Injective fun f : P →* M ↦ (e : M →* N).comp f :=
  LeftInverse.injective (g := (e.symm : N →* M).comp) fun f ↦ by simp [← MonoidHom.comp_assoc]
@[to_additive
  "An additive isomorphism of additive monoids sends `0` to `0`
  (and is hence an additive monoid isomorphism)."]
protected theorem map_one (h : M ≃* N) : h 1 = 1 := map_one h
@[to_additive]
protected theorem map_eq_one_iff (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff
@[to_additive]
theorem map_ne_one_iff (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  EmbeddingLike.map_ne_one_iff
@[to_additive (attr := simps! apply) "A bijective `AddSemigroup` homomorphism is an isomorphism"]
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (hf : Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }
@[to_additive (attr := simp)]
theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Bijective f) :
    f ((ofBijective f hf).symm n) = n := (ofBijective f hf).apply_symm_apply n
@[to_additive "Extract the forward direction of an additive equivalence
  as an addition-preserving function."]
def toMonoidHom (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }
@[to_additive (attr := simp)]
theorem coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e := rfl
@[to_additive (attr := simp)]
theorem toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M →* N) :=
  rfl
@[to_additive]
theorem toMonoidHom_injective : Injective (toMonoidHom : M ≃* N → M →* N) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective
end MulOneClass
@[to_additive (attr := simps apply) "An additive analogue of `Equiv.arrowCongr`,
  where the equivalence between the targets is additive."]
def arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) :
    (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp
@[to_additive (attr := simps apply)
  "An additive analogue of `Equiv.arrowCongr`,
  for additive maps from an additive monoid to a commutative additive monoid."]
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q]
    (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q) where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp
@[to_additive (attr := simps apply)
  "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
  generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.
  This is the `AddEquiv` version of `Equiv.piCongrRight`, and the dependent version of
  `AddEquiv.arrowCongr`."]
def piCongrRight {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with
    toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j),
    map_mul' := fun x y => funext fun j => map_mul (es j) (x j) (y j) }
@[to_additive (attr := simp)]
theorem piCongrRight_refl {η : Type*} {Ms : η → Type*} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ := rfl
@[to_additive (attr := simp)]
theorem piCongrRight_symm {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm := rfl
@[to_additive (attr := simp)]
theorem piCongrRight_trans {η : Type*} {Ms Ns Ps : η → Type*} [∀ j, Mul (Ms j)]
    [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) := rfl
@[to_additive (attr := simps!)
  "A family indexed by a type with a unique element
  is `AddEquiv` to the element at the single index."]
def piUnique {ι : Type*} (M : ι → Type*) [∀ j, Mul (M j)] [Unique ι] :
    (∀ j, M j) ≃* M default :=
  { Equiv.piUnique M with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ :=
  map_inv h x
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  map_div h x y
end MulEquiv
@[to_additive
  "Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and
  `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  homomorphisms."]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul
@[to_additive (attr := simp)]
theorem MulHom.toMulEquiv_apply [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M)
    (h₁ : g.comp f = MulHom.id _) (h₂ : f.comp g = MulHom.id _) :
    ((MulHom.toMulEquiv f g h₁ h₂) : M → N) = f :=
  rfl
@[to_additive (attr := simp)]
theorem MulHom.toMulEquiv_symm_apply [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M)
    (h₁ : g.comp f = MulHom.id _) (h₂ : f.comp g = MulHom.id _) :
    (MulEquiv.symm (MulHom.toMulEquiv f g h₁ h₂) : N → M) = ↑g :=
  rfl
@[to_additive (attr := simps (config := .asFn))
  "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
  and `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`.  This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  monoid homomorphisms."]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul
namespace Equiv
section InvolutiveInv
variable (G) [InvolutiveInv G]
@[to_additive (attr := simps! (config := .asFn) apply)
    "Negation on an `AddGroup` is a permutation of the underlying type."]
protected def inv : Perm G :=
  inv_involutive.toPerm _
variable {G}
@[to_additive (attr := simp)]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl
end InvolutiveInv
end Equiv