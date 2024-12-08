import Mathlib.RingTheory.Coalgebra.TensorProduct
universe v u
namespace CoalgebraCat
variable (R : Type u) [CommRing R]
open CategoryTheory Coalgebra
open scoped TensorProduct MonoidalCategory
@[simps]
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (CoalgebraCat R) where
  tensorObj X Y := of R (X ⊗[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Coalgebra.TensorProduct.map f.1 g.1)
  tensorUnit := CoalgebraCat.of R R
  associator X Y Z := (Coalgebra.TensorProduct.assoc R X Y Z).toCoalgebraCatIso
  leftUnitor X := (Coalgebra.TensorProduct.lid R X).toCoalgebraCatIso
  rightUnitor X := (Coalgebra.TensorProduct.rid R X).toCoalgebraCatIso
@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (CoalgebraCat R) (ModuleCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq X Y Z f := by ext; rfl
  whiskerRight_eq X f := by ext; rfl
  tensorHom_eq f g := by ext; rfl
  εIso := Iso.refl _
  associator_eq X Y Z := TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
  leftUnitor_eq X := TensorProduct.ext <| by ext; rfl
  rightUnitor_eq X := TensorProduct.ext <| by ext; rfl
noncomputable instance instMonoidalCategory : MonoidalCategory (CoalgebraCat R) :=
  Monoidal.induced (forget₂ _ (ModuleCat R)) (MonoidalCategory.inducingFunctorData R)
end CoalgebraCat