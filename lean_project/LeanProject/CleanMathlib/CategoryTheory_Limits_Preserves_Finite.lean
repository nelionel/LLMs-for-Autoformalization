import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
open CategoryTheory
namespace CategoryTheory.Limits
universe u w w₂ v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : Type w} [SmallCategory J] {K : J ⥤ C}
class PreservesFiniteLimits (F : C ⥤ D) : Prop where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance
attribute [instance] PreservesFiniteLimits.preservesFiniteLimits
instance (F : C ⥤ D) : Subsingleton (PreservesFiniteLimits F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)
lemma PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F
instance (priority := 120) PreservesLimitsOfSize0.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F
lemma preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfShape J F) :
    PreservesFiniteLimits F where
      preservesFiniteLimits J (_ : SmallCategory J) _ := by
        letI : Category (ULiftHom (ULift J)) := ULiftHom.category
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F
lemma comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩
lemma preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_natIso h
class PreservesFiniteProducts (F : C ⥤ D) : Prop where
  preserves : ∀ (J : Type) [Fintype J], PreservesLimitsOfShape (Discrete J) F
attribute [instance] PreservesFiniteProducts.preserves
instance (F : C ⥤ D) : Subsingleton (PreservesFiniteProducts F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteProducts F] : PreservesLimitsOfShape (Discrete J) F := by
  apply Nonempty.some
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  exact ⟨preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F⟩
instance comp_preservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G] :
    PreservesFiniteProducts (F ⋙ G) where
  preserves _ _ := inferInstance
instance (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteProducts F where
  preserves _ _ := inferInstance
class ReflectsFiniteLimits (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance
attribute [instance] ReflectsFiniteLimits.reflects
instance (F : C ⥤ D) : Subsingleton (ReflectsFiniteLimits F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
class ReflectsFiniteProducts (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [Fintype J], ReflectsLimitsOfShape (Discrete J) F
attribute [instance] ReflectsFiniteProducts.reflects
instance (F : C ⥤ D) : Subsingleton (ReflectsFiniteProducts F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
lemma ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F
instance (priority := 120) (F : C ⥤ D) [ReflectsLimitsOfSize.{0, 0} F] :
    ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F
instance (priority := 120) (F : C ⥤ D)
    [ReflectsLimits F] : ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F
lemma preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G
lemma preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G
instance reflectsFiniteLimits_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesFiniteLimits F] :
      ReflectsFiniteLimits F where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms
instance reflectsFiniteProducts_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] :
      ReflectsFiniteProducts F where
  reflects _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms
instance comp_reflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteProducts F] [ReflectsFiniteProducts G] :
    ReflectsFiniteProducts (F ⋙ G) where
  reflects _ _ := inferInstance
instance (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsFiniteProducts F where
  reflects _ _ := inferInstance
class PreservesFiniteColimits (F : C ⥤ D) : Prop where
  preservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance
attribute [instance] PreservesFiniteColimits.preservesFiniteColimits
instance (F : C ⥤ D) : Subsingleton (PreservesFiniteColimits F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J)
lemma PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F
instance (priority := 120) PreservesColimitsOfSize0.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F
lemma preservesFiniteColimits_of_preservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColimitsOfShape J F) :
    PreservesFiniteColimits F where
      preservesFiniteColimits J (_ : SmallCategory J) _ := by
        letI : Category (ULiftHom (ULift J)) := ULiftHom.category
        haveI := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F
lemma comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩
lemma preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] :
    PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_natIso h
class PreservesFiniteCoproducts (F : C ⥤ D) : Prop where
  preserves : ∀ (J : Type) [Fintype J], PreservesColimitsOfShape (Discrete J) F
attribute [instance] PreservesFiniteCoproducts.preserves
instance (F : C ⥤ D) : Subsingleton (PreservesFiniteCoproducts F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteCoproducts F] : PreservesColimitsOfShape (Discrete J) F := by
  apply Nonempty.some
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  exact ⟨preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) F⟩
instance comp_preservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G] :
    PreservesFiniteCoproducts (F ⋙ G) where
  preserves _ _ := inferInstance
instance (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteCoproducts F where
  preserves _ _ := inferInstance
class ReflectsFiniteColimits (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F := by
    infer_instance
attribute [instance] ReflectsFiniteColimits.reflects
instance (F : C ⥤ D) : Subsingleton (ReflectsFiniteColimits F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
lemma ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F
instance (priority := 120) (F : C ⥤ D) [ReflectsColimitsOfSize.{0, 0} F] :
    ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F
instance (priority := 120) (F : C ⥤ D)
    [ReflectsColimits F] : ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F
class ReflectsFiniteCoproducts (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [Fintype J], ReflectsColimitsOfShape (Discrete J) F
attribute [instance] ReflectsFiniteCoproducts.reflects
instance (F : C ⥤ D) : Subsingleton (ReflectsFiniteCoproducts F) :=
  ⟨fun ⟨a⟩ ⟨b⟩ => by congr⟩
lemma preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G
lemma preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G
instance reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteColimits C] [PreservesFiniteColimits F] :
      ReflectsFiniteColimits F where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms
instance reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] :
      ReflectsFiniteCoproducts F where
  reflects _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms
instance comp_reflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteCoproducts F] [ReflectsFiniteCoproducts G] :
    ReflectsFiniteCoproducts (F ⋙ G) where
  reflects _ _ := inferInstance
instance (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsFiniteCoproducts F where
  reflects _ _ := inferInstance
end CategoryTheory.Limits