import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Rel
namespace CategoryTheory
universe u
def RelCat :=
  Type u
instance RelCat.inhabited : Inhabited RelCat := by unfold RelCat; infer_instance
instance rel : LargeCategory RelCat where
  Hom X Y := X → Y → Prop
  id _ x y := x = y
  comp f g x z := ∃ y, f x y ∧ g y z
namespace RelCat
@[ext] theorem hom_ext {X Y : RelCat} (f g : X ⟶ Y) (h : ∀ a b, f a b ↔ g a b) : f = g :=
  funext₂ (fun a b => propext (h a b))
namespace Hom
protected theorem rel_id (X : RelCat) : 𝟙 X = (· = ·) := rfl
protected theorem rel_comp {X Y Z : RelCat} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = Rel.comp f g := rfl
theorem rel_id_apply₂ (X : RelCat) (x y : X) : (𝟙 X) x y ↔ x = y := by
  rw [RelCat.Hom.rel_id]
theorem rel_comp_apply₂ {X Y Z : RelCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (f ≫ g) x z ↔ ∃ y, f x y ∧ g y z := by rfl
end Hom
def graphFunctor : Type u ⥤ RelCat.{u} where
  obj X := X
  map f := f.graph
  map_id X := by
    ext
    simp [Hom.rel_id_apply₂]
  map_comp f g := by
    ext
    simp [Hom.rel_comp_apply₂]
@[simp] theorem graphFunctor_map {X Y : Type u} (f : X ⟶ Y) (x : X) (y : Y) :
    graphFunctor.map f x y ↔ f x = y := f.graph_def x y
instance graphFunctor_faithful : graphFunctor.Faithful where
  map_injective h := Function.graph_injective h
instance graphFunctor_essSurj : graphFunctor.EssSurj :=
    graphFunctor.essSurj_of_surj Function.surjective_id
theorem rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) :
    IsIso (C := RelCat) r ↔ ∃ f : (Iso (C := Type u) X Y), graphFunctor.map f.hom = r := by
  constructor
  · intro h
    have h1 := congr_fun₂ h.hom_inv_id
    have h2 := congr_fun₂ h.inv_hom_id
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (h1 a a).mpr rfl)
    obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun a => (h2 a a).mpr rfl)
    suffices hif : IsIso (C := Type u) f by
      use asIso f
      ext x y
      simp only [asIso_hom, graphFunctor_map]
      constructor
      · rintro rfl
        exact (hf x).1
      · intro hr
        specialize h2 (f x) y
        rw [← h2]
        use x, (hf x).2, hr
    use g
    constructor
    · ext x
      apply (h1 _ _).mp
      use f x, (hg _).2, (hf _).2
    · ext y
      apply (h2 _ _).mp
      use g y, (hf (g y)).2, (hg y).2
  · rintro ⟨f, rfl⟩
    apply graphFunctor.map_isIso
section Opposite
open Opposite
def opFunctor : RelCat ⥤ RelCatᵒᵖ where
  obj X := op X
  map {_ _} r := op (fun y x => r x y)
  map_id X := by
    congr
    simp only [unop_op, RelCat.Hom.rel_id]
    ext x y
    exact Eq.comm
  map_comp {X Y Z} f g := by
    unfold Category.opposite
    congr
    ext x y
    apply exists_congr
    exact fun a => And.comm
def unopFunctor : RelCatᵒᵖ ⥤ RelCat where
  obj X := unop X
  map {_ _} r x y := unop r y x
  map_id X := by
    dsimp
    ext x y
    exact Eq.comm
  map_comp {X Y Z} f g := by
    unfold Category.opposite
    ext x y
    apply exists_congr
    exact fun a => And.comm
@[simp] theorem opFunctor_comp_unopFunctor_eq :
    Functor.comp opFunctor unopFunctor = Functor.id _ := rfl
@[simp] theorem unopFunctor_comp_opFunctor_eq :
    Functor.comp unopFunctor opFunctor = Functor.id _ := rfl
@[simps]
def opEquivalence : Equivalence RelCat RelCatᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _
instance : opFunctor.IsEquivalence := by
  change opEquivalence.functor.IsEquivalence
  infer_instance
instance : unopFunctor.IsEquivalence := by
  change opEquivalence.inverse.IsEquivalence
  infer_instance
end Opposite
end RelCat
end CategoryTheory