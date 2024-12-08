import Mathlib.CategoryTheory.Balanced
import Mathlib.CategoryTheory.LiftingProperties.Basic
universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]
variable {P Q : C}
class StrongEpi (f : P ⟶ Q) : Prop where
  epi : Epi f
  llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z
theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y)
      (_ : Mono z) (u : P ⟶ X) (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) :
    StrongEpi f :=
  { epi := inferInstance
    llp := fun {X Y} z hz => ⟨fun {u v} sq => hf X Y z hz u v sq⟩ }
class StrongMono (f : P ⟶ Q) : Prop where
  mono : Mono f
  rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f
theorem StrongMono.mk' {f : P ⟶ Q} [Mono f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (_ : Epi z) (u : X ⟶ P)
      (v : Y ⟶ Q) (sq : CommSq u z f v), sq.HasLift) : StrongMono f where
  mono := inferInstance
  rlp := fun {X Y} z hz => ⟨fun {u v} sq => hf X Y z hz u v sq⟩
attribute [instance 100] StrongEpi.llp
attribute [instance 100] StrongMono.rlp
instance (priority := 100) epi_of_strongEpi (f : P ⟶ Q) [StrongEpi f] : Epi f :=
  StrongEpi.epi
instance (priority := 100) mono_of_strongMono (f : P ⟶ Q) [StrongMono f] : Mono f :=
  StrongMono.mono
section
variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)
theorem strongEpi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }
theorem strongMono_comp [StrongMono f] [StrongMono g] : StrongMono (f ≫ g) :=
  { mono := mono_comp _ _
    rlp := by
      intros
      infer_instance }
theorem strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.assoc, CommSq.fac_right, sq.w], by simp⟩ }
theorem strongMono_of_strongMono [StrongMono (f ≫ g)] : StrongMono f :=
  { mono := mono_of_mono f g
    rlp := fun {X Y} z => by
      intros
      constructor
      intro u v sq
      have h₀ : u ≫ f ≫ g = z ≫ v ≫ g := by
        rw [← Category.assoc, eq_whisker sq.w, Category.assoc]
      exact CommSq.HasLift.mk' ⟨(CommSq.mk h₀).lift, by simp, by simp [← cancel_epi z, sq.w]⟩ }
instance (priority := 100) strongEpi_of_isIso [IsIso f] : StrongEpi f where
  epi := by infer_instance
  llp {_ _} _ := HasLiftingProperty.of_left_iso _ _
instance (priority := 100) strongMono_of_isIso [IsIso f] : StrongMono f where
  mono := by infer_instance
  rlp {_ _} _ := HasLiftingProperty.of_right_iso _ _
theorem StrongEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongEpi f] : StrongEpi g :=
  { epi := by
      rw [Arrow.iso_w' e]
      infer_instance
    llp := fun {X Y} z => by
      intro
      apply HasLiftingProperty.of_arrow_iso_left e z }
theorem StrongMono.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongMono f] : StrongMono g :=
  { mono := by
      rw [Arrow.iso_w' e]
      infer_instance
    rlp := fun {X Y} z => by
      intro
      apply HasLiftingProperty.of_arrow_iso_right z e }
theorem StrongEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongEpi f ↔ StrongEpi g := by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]
theorem StrongMono.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongMono f ↔ StrongMono g := by
  constructor <;> intro
  exacts [StrongMono.of_arrow_iso e, StrongMono.of_arrow_iso e.symm]
end
theorem isIso_of_mono_of_strongEpi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by aesop_cat⟩⟩
theorem isIso_of_epi_of_strongMono (f : P ⟶ Q) [Epi f] [StrongMono f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by aesop_cat⟩⟩
section
variable (C)
class StrongEpiCategory : Prop where
  strongEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f
class StrongMonoCategory : Prop where
  strongMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f
end
theorem strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strongEpi_of_epi _
theorem strongMono_of_mono [StrongMonoCategory C] (f : P ⟶ Q) [Mono f] : StrongMono f :=
  StrongMonoCategory.strongMono_of_mono _
section
attribute [local instance] strongEpi_of_epi
instance (priority := 100) balanced_of_strongEpiCategory [StrongEpiCategory C] : Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_mono_of_strongEpi _
end
section
attribute [local instance] strongMono_of_mono
instance (priority := 100) balanced_of_strongMonoCategory [StrongMonoCategory C] : Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_epi_of_strongMono _
end
end CategoryTheory