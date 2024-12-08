import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
namespace CategoryTheory
universe v v₂ u u₂
variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {X Y : C} (f g : X ⟶ Y)
structure IsSplitEqualizer {W : C} (ι : W ⟶ X) where
  leftRetraction : X ⟶ W
  rightRetraction : Y ⟶ X
  condition : ι ≫ f = ι ≫ g := by aesop_cat
  ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W := by aesop_cat
  bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X := by aesop_cat
  top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι := by aesop_cat
instance {X : C} : Inhabited (IsSplitEqualizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { leftRetraction := 𝟙 X, rightRetraction := 𝟙 X }
open IsSplitEqualizer
attribute [reassoc] condition
attribute [reassoc (attr := simp)] ι_leftRetraction bottom_rightRetraction top_rightRetraction
variable {f g}
@[simps]
def IsSplitEqualizer.map {W : C} {ι : W ⟶ X} (q : IsSplitEqualizer f g ι) (F : C ⥤ D) :
    IsSplitEqualizer (F.map f) (F.map g) (F.map ι) where
  leftRetraction := F.map q.leftRetraction
  rightRetraction := F.map q.rightRetraction
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  ι_leftRetraction := by rw [← F.map_comp, q.ι_leftRetraction, F.map_id]
  bottom_rightRetraction := by rw [← F.map_comp, q.bottom_rightRetraction, F.map_id]
  top_rightRetraction := by rw [← F.map_comp, q.top_rightRetraction, F.map_comp]
section
open Limits
@[simps! pt]
def IsSplitEqualizer.asFork {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    Fork f g := Fork.ofι h t.condition
@[simp]
theorem IsSplitEqualizer.asFork_ι {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    t.asFork.ι = h := rfl
def IsSplitEqualizer.isEqualizer {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    IsLimit t.asFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨ s.ι ≫ t.leftRetraction,
      by simp [- top_rightRetraction, ← t.top_rightRetraction, s.condition_assoc],
      fun hm => by simp [← hm] ⟩
end
variable (f g)
class HasSplitEqualizer : Prop where
  splittable : ∃ (W : C) (h : W ⟶ X), Nonempty (IsSplitEqualizer f g h)
abbrev Functor.IsCosplitPair : Prop :=
  HasSplitEqualizer (G.map f) (G.map g)
noncomputable def HasSplitEqualizer.equalizerOfSplit [HasSplitEqualizer f g] : C :=
  (splittable (f := f) (g := g)).choose
noncomputable def HasSplitEqualizer.equalizerι [HasSplitEqualizer f g] :
    HasSplitEqualizer.equalizerOfSplit f g ⟶ X :=
  (splittable (f := f) (g := g)).choose_spec.choose
noncomputable def HasSplitEqualizer.isSplitEqualizer [HasSplitEqualizer f g] :
    IsSplitEqualizer f g (HasSplitEqualizer.equalizerι f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec
instance map_is_cosplit_pair [HasSplitEqualizer f g] : HasSplitEqualizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitEqualizer.map (HasSplitEqualizer.isSplitEqualizer f g) _⟩⟩
namespace Limits
instance (priority := 1) hasEqualizer_of_hasSplitEqualizer [HasSplitEqualizer f g] :
    HasEqualizer f g :=
  HasLimit.mk ⟨_, (HasSplitEqualizer.isSplitEqualizer f g).isEqualizer⟩
end Limits
end CategoryTheory