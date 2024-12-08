import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
namespace CategoryTheory
universe w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory Functor Category Opposite Discrete Bicategory
variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
@[ext]
structure Pseudofunctor.Grothendieck (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) where
  base : 𝒮
  fiber : F.obj ⟨op base⟩
namespace Pseudofunctor.Grothendieck
scoped prefix:75 "∫ " => Pseudofunctor.Grothendieck
structure Hom (X Y : ∫ F) where
  base : X.base ⟶ Y.base
  fiber : X.fiber ⟶ (F.map base.op.toLoc).obj Y.fiber
@[simps!]
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.app Z.fiber }
section
variable {a b : ∫ F}
@[ext (iff := false)]
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : f.fiber = g.fiber ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  cases f; cases g
  congr
  dsimp at hfg₁
  rw [← conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simpa only [eqToHom_refl, id_comp] using hfg₂
lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ ∃ (hfg : f.base = g.base), f.fiber = g.fiber ≫ eqToHom (hfg ▸ rfl) where
  mp hfg := ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂
lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (h ▸ rfl) := by
  simp [h]
end
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, ← Functor.map_comp_assoc, Strict.leftUnitor_eqToIso]
  assoc f g h := by
    ext
    · simp
    · simp [← NatTrans.naturality_assoc, F.mapComp_assoc_right_inv_app, Strict.associator_eqToIso]
variable (F)
@[simps]
def forget : ∫ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base
end Pseudofunctor.Grothendieck
end CategoryTheory