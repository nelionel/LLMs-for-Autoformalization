import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.PUnitInstances.Algebra
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Algebra.Ring.Action.Group
universe u v
open CategoryTheory
@[to_additive AddMonCat]
def MonCat : Type (u + 1) :=
  Bundled Monoid
add_decl_doc AddMonCat
namespace MonCat
@[to_additive]
abbrev AssocMonoidHom (M N : Type*) [Monoid M] [Monoid N] :=
  MonoidHom M N
add_decl_doc AddMonCat.AssocAddMonoidHom
@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom where
  toFun {_ _} _ _ f := ⇑f
  id _ := MonoidHom.id _
  comp _ _ _ := MonoidHom.comp
deriving instance LargeCategory for MonCat
attribute [to_additive instAddMonCatLargeCategory] instMonCatLargeCategory
@[to_additive]
instance concreteCategory : ConcreteCategory MonCat :=
  BundledHom.concreteCategory _
@[to_additive]
instance : CoeSort MonCat Type* where
  coe X := X.α
@[to_additive]
instance (X : MonCat) : Monoid X := X.str
@[to_additive]
instance {X Y : MonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f
@[to_additive]
instance instFunLike (X Y : MonCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (X →* Y) X Y
@[to_additive]
instance instMonoidHomClass (X Y : MonCat) : MonoidHomClass (X ⟶ Y) X Y :=
  inferInstanceAs <| MonoidHomClass (X →* Y) X Y
@[to_additive (attr := simp)]
lemma coe_id {X : MonCat} : (𝟙 X : X → X) = id := rfl
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : MonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl
@[to_additive (attr := simp)] lemma forget_map {X Y : MonCat} (f : X ⟶ Y) :
    (forget MonCat).map f = f := rfl
@[to_additive (attr := ext)]
lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M
add_decl_doc AddMonCat.of
@[to_additive]
theorem coe_of (R : Type u) [Monoid R] : (MonCat.of R : Type u) = R := rfl
@[to_additive]
instance : Inhabited MonCat :=
  ⟨@of PUnit (@DivInvMonoid.toMonoid _ (@Group.toDivInvMonoid _
    (@CommGroup.toGroup _ PUnit.commGroup)))⟩
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y := f
add_decl_doc AddMonCat.ofHom
@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl
@[to_additive]
instance (X Y : MonCat.{u}) : One (X ⟶ Y) := ⟨ofHom 1⟩
@[to_additive (attr := simp)]
lemma oneHom_apply (X Y : MonCat.{u}) (x : X) : (1 : X ⟶ Y) x = 1 := rfl
@[to_additive (attr := simp)]
lemma one_of {A : Type*} [Monoid A] : (1 : MonCat.of A) = (1 : A) := rfl
@[to_additive (attr := simp)]
lemma mul_of {A : Type*} [Monoid A] (a b : A) :
    @HMul.hMul (MonCat.of A) (MonCat.of A) (MonCat.of A) _ a b = a * b := rfl
@[to_additive]
instance {G : Type*} [Group G] : Group (MonCat.of G) := by assumption
@[to_additive (attr := simps)
  "Universe lift functor for additive monoids."]
def uliftFunctor : MonCat.{u} ⥤ MonCat.{max u v} where
  obj X := MonCat.of (ULift.{v, u} X)
  map {_ _} f := MonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl
end MonCat
@[to_additive AddCommMonCat]
def CommMonCat : Type (u + 1) :=
  Bundled CommMonoid
add_decl_doc AddCommMonCat
namespace CommMonCat
@[to_additive]
instance : BundledHom.ParentProjection @CommMonoid.toMonoid := ⟨⟩
deriving instance LargeCategory for CommMonCat
attribute [to_additive instAddCommMonCatLargeCategory] instCommMonCatLargeCategory
@[to_additive]
instance concreteCategory : ConcreteCategory CommMonCat := by
  dsimp only [CommMonCat]
  infer_instance
@[to_additive]
instance : CoeSort CommMonCat Type* where
  coe X := X.α
@[to_additive]
instance (X : CommMonCat) : CommMonoid X := X.str
@[to_additive]
instance {X Y : CommMonCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f
@[to_additive]
instance instFunLike (X Y : CommMonCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y by infer_instance
@[to_additive (attr := simp)]
lemma coe_id {X : CommMonCat} : (𝟙 X : X → X) = id := rfl
@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommMonCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl
@[to_additive (attr := simp)]
lemma forget_map {X Y : CommMonCat} (f : X ⟶ Y) :
    (forget CommMonCat).map f = (f : X → Y) :=
  rfl
@[to_additive (attr := ext)]
lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMonCat :=
  Bundled.of M
add_decl_doc AddCommMonCat.of
@[to_additive]
instance : Inhabited CommMonCat :=
  ⟨@of PUnit (@CommGroup.toCommMonoid _ PUnit.commGroup)⟩
@[to_additive]
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl
@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat :=
  BundledHom.forget₂ _ _
@[to_additive]
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj
@[to_additive]
def ofHom {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) : of X ⟶ of Y := f
add_decl_doc AddCommMonCat.ofHom
@[to_additive (attr := simp)]
lemma ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl
@[to_additive (attr := simps)
  "Universe lift functor for additive commutative monoids."]
def uliftFunctor : CommMonCat.{u} ⥤ CommMonCat.{max u v} where
  obj X := CommMonCat.of (ULift.{v, u} X)
  map {_ _} f := CommMonCat.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl
end CommMonCat
variable {X Y : Type u}
section
variable [Monoid X] [Monoid Y]
@[to_additive (attr := simps) AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMonCat` from\nan `AddEquiv` between `AddMonoid`s."]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y where
  hom := MonCat.ofHom e.toMonoidHom
  inv := MonCat.ofHom e.symm.toMonoidHom
end
section
variable [CommMonoid X] [CommMonoid Y]
@[to_additive (attr := simps) AddEquiv.toAddCommMonCatIso]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y where
  hom := CommMonCat.ofHom e.toMonoidHom
  inv := CommMonCat.ofHom e.symm.toMonoidHom
add_decl_doc AddEquiv.toAddCommMonCatIso
end
namespace CategoryTheory.Iso
@[to_additive addMonCatIsoToAddEquiv
      "Build an `AddEquiv` from an isomorphism in the category\n`AddMonCat`."]
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
@[to_additive "Build an `AddEquiv` from an isomorphism in the category\n`AddCommMonCat`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id
end CategoryTheory.Iso
@[to_additive addEquivIsoAddMonCatIso]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] :
    X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y where
  hom e := e.toMonCatIso
  inv i := i.monCatIsoToMulEquiv
add_decl_doc addEquivIsoAddMonCatIso
@[to_additive addEquivIsoAddCommMonCatIso]
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y where
  hom e := e.toCommMonCatIso
  inv i := i.commMonCatIsoToMulEquiv
add_decl_doc addEquivIsoAddCommMonCatIso
@[to_additive]
instance MonCat.forget_reflects_isos : (forget MonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact e.toMonCatIso.isIso_hom
@[to_additive]
instance CommMonCat.forget_reflects_isos : (forget CommMonCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommMonCat).map f)
    let e : X ≃* Y := MulEquiv.mk i.toEquiv
      (MonoidHom.map_mul (show MonoidHom X Y from f))
    exact e.toCommMonCatIso.isIso_hom
@[to_additive]
instance CommMonCat.forget₂_full : (forget₂ CommMonCat MonCat).Full where
  map_surjective f := ⟨f, rfl⟩
example : (forget₂ CommMonCat MonCat).ReflectsIsomorphisms := inferInstance
@[to_additive (attr := simp)] theorem MonoidHom.comp_id_monCat
    {G : MonCat.{u}} {H : Type u} [Monoid H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (MonCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_monCat_comp
    {G : Type u} [Monoid G] {H : MonCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (MonCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.comp_id_commMonCat
    {G : CommMonCat.{u}} {H : Type u} [CommMonoid H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommMonCat.ofHom f)
@[to_additive (attr := simp)] theorem MonoidHom.id_commMonCat_comp
    {G : Type u} [CommMonoid G] {H : CommMonCat.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommMonCat.ofHom f)