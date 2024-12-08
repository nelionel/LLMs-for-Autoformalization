import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Filtered.Basic
universe w v v₁ u u₁
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]
namespace IsFiltered
section FilteredClosure
variable [IsFilteredOrEmpty C] {α : Type w} (f : α → C)
inductive FilteredClosure : C → Prop
  | base : (x : α) → FilteredClosure (f x)
  | max : {j j' : C} → FilteredClosure j → FilteredClosure j' → FilteredClosure (max j j')
  | coeq : {j j' : C} → FilteredClosure j → FilteredClosure j' → (f f' : j ⟶ j') →
      FilteredClosure (coeq f f')
instance : IsFilteredOrEmpty (FullSubcategory (FilteredClosure f)) where
  cocone_objs j j' :=
    ⟨⟨max j.1 j'.1, FilteredClosure.max j.2 j'.2⟩, leftToMax _ _, rightToMax _ _, trivial⟩
  cocone_maps {j j'} f f' :=
    ⟨⟨coeq f f', FilteredClosure.coeq j.2 j'.2 f f'⟩, coeqHom (C := C) f f', coeq_condition _ _⟩
namespace FilteredClosureSmall
private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | max : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | coeq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X
private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.max hk hk' x y) => max ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.coeq _ _ _ _ f g) => coeq f g
@[semireducible] private noncomputable def bundledAbstractFilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractFilteredClosure m)⟩
private noncomputable def AbstractFilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractFilteredClosure f n).1
private noncomputable def abstractFilteredClosureRealization : AbstractFilteredClosure f → C :=
  fun x => (bundledAbstractFilteredClosure f x.1).2 x.2
end FilteredClosureSmall
theorem small_fullSubcategory_filteredClosure :
    Small.{max v w} (FullSubcategory (FilteredClosure f)) := by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x => exact ⟨⟨0, ⟨x⟩⟩, rfl⟩
  | max hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, FilteredClosureSmall.InductiveStep.max ?_ ?_ x y⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
  | coeq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, FilteredClosureSmall.InductiveStep.coeq ?_ ?_ x y g g'⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
instance : EssentiallySmall.{max v w} (FullSubcategory (FilteredClosure f)) :=
  have : LocallySmall.{max v w} (FullSubcategory (FilteredClosure f)) := locallySmall_max.{w, v, u}
  have := small_fullSubcategory_filteredClosure f
  essentiallySmall_of_small_of_locallySmall _
end FilteredClosure
section
variable [IsFilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)
def SmallFilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (FullSubcategory (FilteredClosure F.obj))
noncomputable instance : SmallCategory (SmallFilteredIntermediate F) :=
  show SmallCategory (SmallModel (FullSubcategory (FilteredClosure F.obj))) from inferInstance
namespace SmallFilteredIntermediate
noncomputable def factoring : D ⥤ SmallFilteredIntermediate F :=
  FullSubcategory.lift _ F FilteredClosure.base ⋙ (equivSmallModel _).functor
noncomputable def inclusion : SmallFilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _
instance : (inclusion F).Faithful :=
  show ((equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _).Faithful from inferInstance
noncomputable instance : (inclusion F).Full :=
  show ((equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _).Full from inferInstance
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  isoWhiskerLeft _ (isoWhiskerRight (Equivalence.unitIso _).symm _)
instance : IsFilteredOrEmpty (SmallFilteredIntermediate F) :=
  IsFilteredOrEmpty.of_equivalence (equivSmallModel _)
instance [Nonempty D] : IsFiltered (SmallFilteredIntermediate F) :=
  { (inferInstance : IsFilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }
end SmallFilteredIntermediate
end
end IsFiltered
namespace IsCofiltered
section CofilteredClosure
variable [IsCofilteredOrEmpty C] {α : Type w} (f : α → C)
inductive CofilteredClosure : C → Prop
  | base : (x : α) → CofilteredClosure (f x)
  | min : {j j' : C} → CofilteredClosure j → CofilteredClosure j' → CofilteredClosure (min j j')
  | eq : {j j' : C} → CofilteredClosure j → CofilteredClosure j' → (f f' : j ⟶ j') →
      CofilteredClosure (eq f f')
instance : IsCofilteredOrEmpty (FullSubcategory (CofilteredClosure f)) where
  cone_objs j j' :=
    ⟨⟨min j.1 j'.1, CofilteredClosure.min j.2 j'.2⟩, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps {j j'} f f' :=
    ⟨⟨eq f f', CofilteredClosure.eq j.2 j'.2 f f'⟩, eqHom (C := C) f f', eq_condition _ _⟩
namespace CofilteredClosureSmall
private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | min : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | eq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X
private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.min hk hk' x y) => min ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.eq _ _ _ _ f g) => eq f g
@[semireducible] private noncomputable def bundledAbstractCofilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractCofilteredClosure m)⟩
private noncomputable def AbstractCofilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractCofilteredClosure f n).1
private noncomputable def abstractCofilteredClosureRealization : AbstractCofilteredClosure f → C :=
  fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2
end CofilteredClosureSmall
theorem small_fullSubcategory_cofilteredClosure :
    Small.{max v w} (FullSubcategory (CofilteredClosure f)) := by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x => exact ⟨⟨0, ⟨x⟩⟩, rfl⟩
  | min hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, CofilteredClosureSmall.InductiveStep.min ?_ ?_ x y⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
  | eq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, CofilteredClosureSmall.InductiveStep.eq ?_ ?_ x y g g'⟩, rfl⟩
    all_goals apply Nat.lt_succ_of_le
    exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
instance : EssentiallySmall.{max v w} (FullSubcategory (CofilteredClosure f)) :=
  have : LocallySmall.{max v w} (FullSubcategory (CofilteredClosure f)) :=
    locallySmall_max.{w, v, u}
  have := small_fullSubcategory_cofilteredClosure f
  essentiallySmall_of_small_of_locallySmall _
end CofilteredClosure
section
variable [IsCofilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)
def SmallCofilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (FullSubcategory (CofilteredClosure F.obj))
noncomputable instance : SmallCategory (SmallCofilteredIntermediate F) :=
  show SmallCategory (SmallModel (FullSubcategory (CofilteredClosure F.obj))) from inferInstance
namespace SmallCofilteredIntermediate
noncomputable def factoring : D ⥤ SmallCofilteredIntermediate F :=
  FullSubcategory.lift _ F CofilteredClosure.base ⋙ (equivSmallModel _).functor
noncomputable def inclusion : SmallCofilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _
instance : (inclusion F).Faithful :=
  show ((equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _).Faithful from inferInstance
noncomputable instance : (inclusion F).Full :=
  show ((equivSmallModel _).inverse ⋙ fullSubcategoryInclusion _).Full from inferInstance
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  isoWhiskerLeft _ (isoWhiskerRight (Equivalence.unitIso _).symm _)
instance : IsCofilteredOrEmpty (SmallCofilteredIntermediate F) :=
  IsCofilteredOrEmpty.of_equivalence (equivSmallModel _)
instance [Nonempty D] : IsCofiltered (SmallCofilteredIntermediate F) :=
  { (inferInstance : IsCofilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }
end SmallCofilteredIntermediate
end
end IsCofiltered
end CategoryTheory