import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LocallySurjective
universe v v' u u'
open CategoryTheory
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
namespace SheafOfModules
variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
@[simps]
noncomputable def restrictScalars :
    SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R where
  obj M' :=
    { val := (PresheafOfModules.restrictScalars α.val).obj M'.val
      isSheaf := M'.isSheaf }
  map φ := { val := (PresheafOfModules.restrictScalars α.val).map φ.val }
instance : (restrictScalars.{v} α).Additive where
end SheafOfModules
namespace PresheafOfModules
variable {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M₁ M₂ : PresheafOfModules.{v} R'}
noncomputable def restrictHomEquivOfIsLocallySurjective
    (hM₂ : Presheaf.IsSheaf J M₂.presheaf) [Presheaf.IsLocallySurjective J α] :
    (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ ⟶ (restrictScalars α).obj M₂) where
  toFun f := (restrictScalars α).map f
  invFun g := homMk ((toPresheaf R).map g) (fun X r' m ↦ by
    apply hM₂.isSeparated _ _ (Presheaf.imageSieve_mem J α r')
    rintro Y p ⟨r : R.obj _, hr⟩
    have hg : ∀ (z : M₁.obj X), g.app _ (M₁.map p.op z) = M₂.map p.op (g.app X z) :=
      fun z ↦ congr_fun ((forget _).congr_map (g.naturality p.op)) z
    change M₂.map p.op (g.app X (r' • m)) = M₂.map p.op (r' • show M₂.obj X from g.app X m)
    dsimp at hg ⊢
    rw [← hg, M₂.map_smul, ← hg, ← hr]
    erw [← (g.app _).map_smul]
    rw [M₁.map_smul, ← hr]
    rfl)
  left_inv _ := rfl
  right_inv _ := rfl
end PresheafOfModules