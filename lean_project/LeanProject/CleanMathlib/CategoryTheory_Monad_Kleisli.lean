import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Basic
namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]
@[nolint unusedArguments]
def Kleisli (_T : Monad C) :=
  C
namespace Kleisli
variable (T : Monad C)
instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) :=
  ⟨(default : C)⟩
instance category : Category (Kleisli T) where
  Hom := fun X Y : C => X ⟶ (T : C ⥤ C).obj Y
  id X := T.η.app X
  comp {_} {_} {Z} f g := f ≫ (T : C ⥤ C).map g ≫ T.μ.app Z
  id_comp {X} {Y} f := by
    dsimp 
    rw [← T.η.naturality_assoc f, T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp only [Functor.map_comp, Category.assoc, Monad.assoc]
    erw [T.μ.naturality_assoc]
namespace Adjunction
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := (X : Kleisli T)
  map {X} {Y} f := (f ≫ T.η.app Y : X ⟶ T.obj Y)
  map_comp {X} {Y} {Z} f g := by
    change _ = (f ≫ (Monad.η T).app Y) ≫ T.map (g ≫ (Monad.η T).app Z) ≫ T.μ.app Z
    simp [← T.η.naturality g]
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X
  map {_} {Y} f := T.map f ≫ T.μ.app Y
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    change T.map (f ≫ T.map g ≫ T.μ.app Z) ≫ T.μ.app Z = _
    simp only [Functor.map_comp, Category.assoc]
    rw [← T.μ.naturality_assoc g, T.assoc]
    rfl
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (X ⟶ T.obj Y)
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        change f ≫ g = (f ≫ T.η.app Y) ≫ T.map g ≫ T.μ.app Z
        rw [Category.assoc, ← T.η.naturality_assoc g, Functor.id_map]
        dsimp
        simp [Monad.left_unit] }
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _
end Adjunction
end Kleisli
@[nolint unusedArguments]
def Cokleisli (_U : Comonad C) :=
  C
namespace Cokleisli
variable (U : Comonad C)
instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) :=
  ⟨(default : C)⟩
instance category : Category (Cokleisli U) where
  Hom := fun X Y : C => (U : C ⥤ C).obj X ⟶ Y
  id X := U.ε.app X
  comp {X} {_} {_} f g := U.δ.app X ≫ (U : C ⥤ C).map f ≫ g
  id_comp f := by dsimp; rw [U.right_counit_assoc]
  assoc {X} {Y} {Z} {W} f g h := by
    change U.δ.app X ≫ U.map (U.δ.app X ≫ U.map f ≫ g) ≫ h =
      U.δ.app X ≫ U.map f ≫ (U.δ.app Y ≫ U.map g ≫ h)
    simp only [Functor.map_comp, ← Category.assoc, eq_whisker]
    simp only [Category.assoc, U.δ.naturality, Functor.comp_map, U.coassoc_assoc]
namespace Adjunction
@[simps]
def toCokleisli : C ⥤ Cokleisli U where
  obj X := (X : Cokleisli U)
  map {X} {_} f := (U.ε.app X ≫ f : _)
  map_comp {X} {Y} {_} f g := by
    change U.ε.app X ≫ f ≫ g = U.δ.app X ≫ U.map (U.ε.app X ≫ f) ≫ U.ε.app Y ≫ g
    simp [← U.ε.naturality g]
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X
  map {X} {_} f := U.δ.app X ≫ U.map f
  map_id _ := U.right_counit _
  map_comp {X} {Y} {_} f g := by
    change U.δ.app X ≫ U.map (U.δ.app X ≫ U.map f ≫ g) =
      (U.δ.app X ≫ U.map f) ≫ (U.δ.app Y ≫ U.map g)
    simp only [Functor.map_comp, ← Category.assoc]
    rw [Comonad.coassoc]
    simp only [Category.assoc, NatTrans.naturality, Functor.comp_map]
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (U.obj X ⟶ Y)
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by
        change f ≫ g = U.δ.app X ≫ U.map f ≫ U.ε.app Y ≫ g
        rw [← Category.assoc (U.map f), U.ε.naturality]; dsimp
        simp only [← Category.assoc, Comonad.left_counit, Category.id_comp] }
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _
end Adjunction
end Cokleisli
end CategoryTheory