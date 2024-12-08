import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf
universe v v' u u'
open CategoryTheory
namespace PresheafOfModules
variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}
@[simps]
noncomputable def restrictScalarsObj (M' : PresheafOfModules.{v} R') (α : R ⟶ R') :
    PresheafOfModules R where
  obj := fun X ↦ (ModuleCat.restrictScalars (α.app X)).obj (M'.obj X)
  map := fun {X Y} f ↦
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x ↦ (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl ) }
@[simps]
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := M'.restrictScalarsObj α
  map φ' :=
    { app := fun X ↦ (ModuleCat.restrictScalars (α.app X)).map (Hom.app φ' X)
      naturality := fun {X Y} f ↦ by
        ext x
        exact naturality_apply φ' f x }
instance (α : R ⟶ R') : (restrictScalars.{v} α).Additive where
instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full
instance (α : R ⟶ R') : (restrictScalars α).Faithful where
  map_injective h := (toPresheaf R').map_injective ((toPresheaf R).congr_map h)
noncomputable def restrictScalarsCompToPresheaf (α : R ⟶ R') :
    restrictScalars.{v} α ⋙ toPresheaf R ≅ toPresheaf R' := Iso.refl _
end PresheafOfModules