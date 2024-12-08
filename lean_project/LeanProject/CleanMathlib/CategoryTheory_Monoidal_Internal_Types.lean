import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric
universe v u
open CategoryTheory
namespace MonTypeEquivalenceMon
instance monMonoid (A : Mon_ (Type u)) : Monoid A.X where
  one := A.one PUnit.unit
  mul x y := A.mul (x, y)
  one_mul x := by convert congr_fun A.one_mul (PUnit.unit, x)
  mul_one x := by convert congr_fun A.mul_one (x, PUnit.unit)
  mul_assoc x y z := by convert congr_fun A.mul_assoc ((x, y), z)
noncomputable def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f :=
    { toFun := f.hom
      map_one' := congr_fun f.one_hom PUnit.unit
      map_mul' := fun x y => congr_fun f.mul_hom (x, y) }
noncomputable def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A :=
    { X := A
      one := fun _ => 1
      mul := fun p => p.1 * p.2
      one_mul := by ext ⟨_, _⟩; dsimp; simp
      mul_one := by ext ⟨_, _⟩; dsimp; simp
      mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [mul_assoc] }
  map f := { hom := f }
end MonTypeEquivalenceMon
open MonTypeEquivalenceMon
noncomputable def monTypeEquivalenceMon : Mon_ (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl } })
      (by aesop_cat)
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)
noncomputable instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩
namespace CommMonTypeEquivalenceCommMon
instance commMonCommMonoid (A : CommMon_ (Type u)) : CommMonoid A.X :=
  { MonTypeEquivalenceMon.monMonoid A.toMon_ with
    mul_comm := fun x y => by convert congr_fun A.mul_comm (y, x) }
noncomputable def functor : CommMon_ (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := MonTypeEquivalenceMon.functor.map f
noncomputable def inverse : CommMonCat.{u} ⥤ CommMon_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      mul_comm := by
        ext ⟨x : A, y : A⟩
        exact CommMonoid.mul_comm y x }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f)
end CommMonTypeEquivalenceCommMon
open CommMonTypeEquivalenceCommMon
noncomputable def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl } })
      (by aesop_cat)
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)
noncomputable instance commMonTypeInhabited : Inhabited (CommMon_ (Type u)) :=
  ⟨CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of PUnit)⟩