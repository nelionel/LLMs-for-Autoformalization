import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
namespace CategoryTheory
universe v v₂ u u₂
variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {X Y : C} (f g : X ⟶ Y)
structure IsSplitCoequalizer {Z : C} (π : Y ⟶ Z) where
  rightSection : Z ⟶ Y
  leftSection : Y ⟶ X
  condition : f ≫ π = g ≫ π := by aesop_cat
  rightSection_π : rightSection ≫ π = 𝟙 Z := by aesop_cat
  leftSection_bottom : leftSection ≫ g = 𝟙 Y := by aesop_cat
  leftSection_top : leftSection ≫ f = π ≫ rightSection := by aesop_cat
instance {X : C} : Inhabited (IsSplitCoequalizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { rightSection := 𝟙 X, leftSection := 𝟙 X }
open IsSplitCoequalizer
attribute [reassoc] condition
attribute [reassoc (attr := simp)] rightSection_π leftSection_bottom leftSection_top
variable {f g}
@[simps]
def IsSplitCoequalizer.map {Z : C} {π : Y ⟶ Z} (q : IsSplitCoequalizer f g π) (F : C ⥤ D) :
    IsSplitCoequalizer (F.map f) (F.map g) (F.map π) where
  rightSection := F.map q.rightSection
  leftSection := F.map q.leftSection
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  rightSection_π := by rw [← F.map_comp, q.rightSection_π, F.map_id]
  leftSection_bottom := by rw [← F.map_comp, q.leftSection_bottom, F.map_id]
  leftSection_top := by rw [← F.map_comp, q.leftSection_top, F.map_comp]
section
open Limits
@[simps! pt]
def IsSplitCoequalizer.asCofork {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    Cofork f g := Cofork.ofπ h t.condition
@[simp]
theorem IsSplitCoequalizer.asCofork_π {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    t.asCofork.π = h := rfl
def IsSplitCoequalizer.isCoequalizer {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    IsColimit t.asCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨t.rightSection ≫ s.π, by
      dsimp
      rw [← t.leftSection_top_assoc, s.condition, t.leftSection_bottom_assoc], fun hm => by
      simp [← hm]⟩
end
variable (f g)
class HasSplitCoequalizer : Prop where
  splittable : ∃ (Z : C) (h : Y ⟶ Z), Nonempty (IsSplitCoequalizer f g h)
abbrev Functor.IsSplitPair : Prop :=
  HasSplitCoequalizer (G.map f) (G.map g)
noncomputable def HasSplitCoequalizer.coequalizerOfSplit [HasSplitCoequalizer f g] : C :=
  (splittable (f := f) (g := g)).choose
noncomputable def HasSplitCoequalizer.coequalizerπ [HasSplitCoequalizer f g] :
    Y ⟶ HasSplitCoequalizer.coequalizerOfSplit f g :=
  (splittable (f := f) (g := g)).choose_spec.choose
noncomputable def HasSplitCoequalizer.isSplitCoequalizer [HasSplitCoequalizer f g] :
    IsSplitCoequalizer f g (HasSplitCoequalizer.coequalizerπ f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec
instance map_is_split_pair [HasSplitCoequalizer f g] : HasSplitCoequalizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitCoequalizer.map (HasSplitCoequalizer.isSplitCoequalizer f g) _⟩⟩
namespace Limits
instance (priority := 1) hasCoequalizer_of_hasSplitCoequalizer [HasSplitCoequalizer f g] :
    HasCoequalizer f g :=
  HasColimit.mk ⟨_, (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer⟩
end Limits
end CategoryTheory