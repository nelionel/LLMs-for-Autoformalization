import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.ULift
universe w₁ v₁ v₂ u₁ u₂
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
@[simps]
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map f := f
@[simps]
def ULift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map f := f
@[simps]
def ULift.equivalence : C ≌ ULift.{u₂} C where
  functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom :=
        { app := fun _ => 𝟙 _
          naturality := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp }
      inv :=
        { app := fun _ => 𝟙 _
          naturality := fun X Y f => by
            change f ≫ 𝟙 _ = 𝟙 _ ≫ f
            simp }
      hom_inv_id := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        ext
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp }
  functor_unitIso_comp X := by
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp
section ULiftHom
def ULiftHom.{w,u} (C : Type u) : Type u :=
  let _ := ULift.{w} C
  C
instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(default : C)⟩
def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A
def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A
@[simp]
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl
@[simp]
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl
instance ULiftHom.category : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  Hom A B := ULift.{v₂} <| A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩
@[simps]
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map f := ⟨f⟩
@[simps]
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map f := f.down
def ULiftHom.equiv : C ≌ ULiftHom C where
  functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl
end ULiftHom
@[nolint unusedArguments]
def AsSmall.{w, v, u} (D : Type u) [Category.{v} D] := ULift.{max w v} D
instance : SmallCategory (AsSmall.{w₁} C) where
  Hom X Y := ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩
@[simps]
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map f := ⟨f⟩
@[simps]
def AsSmall.down : AsSmall C ⥤ C where
  obj X := ULift.down X
  map f := f.down
@[reassoc]
theorem down_comp {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.down ≫ g.down :=
  rfl
@[simp]
theorem eqToHom_down {X Y : AsSmall C} (h : X = Y) :
    (eqToHom h).down = eqToHom (congrArg ULift.down h) := by
  subst h
  rfl
@[simps]
def AsSmall.equiv : C ≌ AsSmall C where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso <| ULift.ext _ _ rfl
instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨default⟩⟩
def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv
end CategoryTheory