import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EssentiallySmall
universe v u₁ u₂
namespace CategoryTheory
variable (C : Type u₁) [Category.{v} C]
class WellPowered : Prop where
  subobject_small : ∀ X : C, Small.{v} (Subobject X) := by infer_instance
instance small_subobject [WellPowered C] (X : C) : Small.{v} (Subobject X) :=
  WellPowered.subobject_small X
instance (priority := 100) wellPowered_of_smallCategory (C : Type u₁) [SmallCategory C] :
    WellPowered C where
variable {C}
theorem essentiallySmall_monoOver_iff_small_subobject (X : C) :
    EssentiallySmall.{v} (MonoOver X) ↔ Small.{v} (Subobject X) :=
  essentiallySmall_iff_of_thin
theorem wellPowered_of_essentiallySmall_monoOver (h : ∀ X : C, EssentiallySmall.{v} (MonoOver X)) :
    WellPowered C :=
  { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }
section
variable [WellPowered C]
instance essentiallySmall_monoOver (X : C) : EssentiallySmall.{v} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)
end
section Equivalence
variable {D : Type u₂} [Category.{v} D]
theorem wellPowered_of_equiv (e : C ≌ D) [WellPowered C] : WellPowered D :=
  wellPowered_of_essentiallySmall_monoOver fun X =>
    (essentiallySmall_congr (MonoOver.congr X e.symm)).2 <| by infer_instance
theorem wellPowered_congr (e : C ≌ D) : WellPowered C ↔ WellPowered D :=
  ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩
end Equivalence
end CategoryTheory