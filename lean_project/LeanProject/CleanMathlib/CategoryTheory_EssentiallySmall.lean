import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Logic.UnivLE
import Mathlib.Logic.Small.Basic
universe w v v' u u'
open CategoryTheory
variable (C : Type u) [Category.{v} C]
namespace CategoryTheory
@[pp_with_univ]
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩
@[pp_with_univ]
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)
noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : SmallCategory (SmallModel C) :=
  Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    C ≌ SmallModel C :=
  Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))
instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : EssentiallySmall.{w} Cᵒᵖ :=
  EssentiallySmall.mk' (equivSmallModel C).op
theorem essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)
theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩
theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)
@[pp_with_univ]
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by infer_instance
instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small.{w, v} (X ⟶ Y) :=
  LocallySmall.hom_small X Y
theorem locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C where
  hom_small {_ _} := small_of_injective F.map_injective
theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩
instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] :
    LocallySmall.{v} C where
instance (priority := 100) locallySmall_of_univLE (C : Type u) [Category.{v} C] [UnivLE.{v, w}] :
    LocallySmall.{w} C where
theorem locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C where
  hom_small _ _ := small_max.{w} _
instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)
@[pp_with_univ]
def ShrinkHoms (C : Type u) :=
  C
namespace ShrinkHoms
section
variable {C' : Type*}
def toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C' :=
  X
def fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C' :=
  X
@[simp]
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl
@[simp]
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl
end
variable [LocallySmall.{w} C]
@[simps]
noncomputable instance : Category.{w} (ShrinkHoms C) where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)
@[simps]
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj X := toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f
@[simps]
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj X := fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f
@[simps]
noncomputable def equivalence : C ≌ ShrinkHoms C where
  functor := functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
end ShrinkHoms
namespace Shrink
noncomputable instance [Small.{w} C] : Category.{v} (Shrink.{w} C) :=
  InducedCategory.category (equivShrink C).symm
noncomputable def equivalence [Small.{w} C] : C ≌ Shrink.{w} C :=
  (inducedFunctor (equivShrink C).symm).asEquivalence.symm
end Shrink
theorem essentiallySmall_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C := by
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEquiv.symm
    letI : Category S := InducedCategory.category (e'.trans e).symm
    refine ⟨⟨S, this, ⟨?_⟩⟩⟩
    refine (ShrinkHoms.equivalence C).trans <|
      (skeletonEquivalence (ShrinkHoms C)).symm.trans
        ((inducedFunctor (e'.trans e).symm).asEquivalence.symm)
theorem essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩
section FullSubcategory
instance locallySmall_fullSubcategory [LocallySmall.{w} C] (P : C → Prop) :
    LocallySmall.{w} (FullSubcategory P) :=
  locallySmall_of_faithful <| fullSubcategoryInclusion P
instance essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySmall.{w} C] :
    EssentiallySmall.{w} (FullSubcategory (· ∈ s)) :=
  suffices Small.{w} (FullSubcategory (· ∈ s)) from essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by aesop_cat)
end FullSubcategory
instance (priority := 100) locallySmall_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    LocallySmall.{w} C where
theorem essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]
instance [Small.{w} C] : Small.{w} (Discrete C) := small_map discreteEquiv
end CategoryTheory