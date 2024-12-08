import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct.Basic
open CategoryTheory
open scoped MonoidalCategory
universe v u
variable {R : Type u} [CommRing R]
namespace AlgebraCat
noncomputable section
namespace instMonoidalCategory
open scoped TensorProduct
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgebraCat.{u} R) : AlgebraCat.{u} R :=
  of R (X ⊗[R] Y)
noncomputable abbrev tensorHom {W X Y Z : AlgebraCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ofHom <| Algebra.TensorProduct.map f.hom g.hom
open MonoidalCategory
end instMonoidalCategory
open instMonoidalCategory
instance : MonoidalCategoryStruct (AlgebraCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso
noncomputable instance instMonoidalCategory : MonoidalCategory (AlgebraCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgebraCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ => TensorProduct.ext_threefold (fun _ _ _ => rfl)
      leftUnitor_eq := fun _ => TensorProduct.ext' (fun _ _ => rfl)
      rightUnitor_eq := fun _ => TensorProduct.ext' (fun _ _ => rfl) }
example : (forget₂ (AlgebraCat R) (ModuleCat R)).Monoidal := inferInstance
end
end AlgebraCat