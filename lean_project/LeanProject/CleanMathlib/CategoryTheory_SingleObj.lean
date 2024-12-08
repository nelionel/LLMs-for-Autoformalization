import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Combinatorics.Quiver.SingleObj
import Mathlib.Algebra.Group.Units.Equiv
universe u v w
namespace CategoryTheory
abbrev SingleObj :=
  Quiver.SingleObj
namespace SingleObj
variable (M G : Type u)
instance categoryStruct [One M] [Mul M] : CategoryStruct (SingleObj M) where
  Hom _ _ := M
  comp x y := y * x
  id _ := 1
variable [Monoid M] [Group G]
instance category : Category (SingleObj M) where
  comp_id := one_mul
  id_comp := mul_one
  assoc x y z := (mul_assoc z y x).symm
theorem id_as_one (x : SingleObj M) : 𝟙 x = 1 :=
  rfl
theorem comp_as_mul {x y z : SingleObj M} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl
instance finCategoryOfFintype (M : Type) [Fintype M] [Monoid M] : FinCategory (SingleObj M) where
instance groupoid : Groupoid (SingleObj G) where
  inv x := x⁻¹
  inv_comp := mul_inv_cancel
  comp_inv := inv_mul_cancel
theorem inv_as_inv {x y : SingleObj G} (f : x ⟶ y) : inv f = f⁻¹ := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [comp_as_mul, inv_mul_cancel, id_as_one]
abbrev star : SingleObj M :=
  Quiver.SingleObj.star M
def toEnd : M ≃* End (SingleObj.star M) :=
  { Equiv.refl M with map_mul' := fun _ _ => rfl }
theorem toEnd_def (x : M) : toEnd M x = x :=
  rfl
variable (N : Type v) [Monoid N]
def mapHom : (M →* N) ≃ SingleObj M ⥤ SingleObj N where
  toFun f :=
    { obj := id
      map := ⇑f
      map_id := fun _ => f.map_one
      map_comp := fun x y => f.map_mul y x }
  invFun f :=
    { toFun := fun x => f.map ((toEnd M) x)
      map_one' := f.map_id _
      map_mul' := fun x y => f.map_comp y x }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
theorem mapHom_id : mapHom M M (MonoidHom.id M) = 𝟭 _ :=
  rfl
variable {M N G}
theorem mapHom_comp (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    mapHom M P (g.comp f) = mapHom M N f ⋙ mapHom N P g :=
  rfl
variable {C : Type v} [Category.{w} C]
@[simps]
def differenceFunctor (f : C → G) : C ⥤ SingleObj G where
  obj _ := ()
  map {x y} _ := f y * (f x)⁻¹
  map_id := by
    intro
    simp only [SingleObj.id_as_one, mul_inv_cancel]
  map_comp := by
    intros
    dsimp
    rw [SingleObj.comp_as_mul, ← mul_assoc, mul_left_inj, mul_assoc, inv_mul_cancel, mul_one]
@[simps]
def functor {X : C} (f : M →* End X) : SingleObj M ⥤ C where
  obj _ := X
  map a := f a
  map_id _ := MonoidHom.map_one f
  map_comp a b := MonoidHom.map_mul f b a
@[simps]
def natTrans {F G : SingleObj M ⥤ C} (u : F.obj (SingleObj.star M) ⟶ G.obj (SingleObj.star M))
    (h : ∀ a : M, F.map a ≫ u = u ≫ G.map a) : F ⟶ G where
  app _ := u
  naturality _ _ a := h a
end SingleObj
end CategoryTheory
open CategoryTheory
namespace MonoidHom
variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]
abbrev toFunctor (f : M →* N) : SingleObj M ⥤ SingleObj N :=
  SingleObj.mapHom M N f
@[simp]
theorem comp_toFunctor (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl
variable (M)
@[simp]
theorem id_toFunctor : (id M).toFunctor = 𝟭 _ :=
  rfl
end MonoidHom
namespace MulEquiv
variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]
@[simps!]
def toSingleObjEquiv (e : M ≃* N) : SingleObj M ≌ SingleObj N where
  functor := e.toMonoidHom.toFunctor
  inverse := e.symm.toMonoidHom.toFunctor
  unitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    aesop_cat)
  counitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    aesop_cat)
end MulEquiv
namespace Units
variable (M : Type u) [Monoid M]
def toAut : Mˣ ≃* Aut (SingleObj.star M) :=
  MulEquiv.trans (Units.mapEquiv (SingleObj.toEnd M))
    (Aut.unitsEndEquivAut (SingleObj.star M))
@[simp]
theorem toAut_hom (x : Mˣ) : (toAut M x).hom = SingleObj.toEnd M x :=
  rfl
@[simp]
theorem toAut_inv (x : Mˣ) : (toAut M x).inv = SingleObj.toEnd M (x⁻¹ : Mˣ) :=
  rfl
end Units
namespace MonCat
open CategoryTheory
def toCat : MonCat ⥤ Cat where
  obj x := Cat.of (SingleObj x)
  map {x y} f := SingleObj.mapHom x y f
instance toCat_full : toCat.Full where
  map_surjective := (SingleObj.mapHom _ _).surjective
instance toCat_faithful : toCat.Faithful where
  map_injective h := by rwa [toCat, (SingleObj.mapHom _ _).apply_eq_iff_eq] at h
end MonCat