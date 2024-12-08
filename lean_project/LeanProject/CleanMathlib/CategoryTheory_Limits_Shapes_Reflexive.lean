import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
namespace CategoryTheory
universe v v₂ u u₂
variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A B : C} {f g : A ⟶ B}
class IsReflexivePair (f g : A ⟶ B) : Prop where
  common_section' : ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B
theorem IsReflexivePair.common_section (f g : A ⟶ B) [IsReflexivePair f g] :
    ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B := IsReflexivePair.common_section'
class IsCoreflexivePair (f g : A ⟶ B) : Prop where
  common_retraction' : ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A
theorem IsCoreflexivePair.common_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A := IsCoreflexivePair.common_retraction'
theorem IsReflexivePair.mk' (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B) :
    IsReflexivePair f g :=
  ⟨⟨s, sf, sg⟩⟩
theorem IsCoreflexivePair.mk' (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A) :
    IsCoreflexivePair f g :=
  ⟨⟨s, fs, gs⟩⟩
noncomputable def commonSection (f g : A ⟶ B) [IsReflexivePair f g] : B ⟶ A :=
  (IsReflexivePair.common_section f g).choose
@[reassoc (attr := simp)]
theorem section_comp_left (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ f = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.1
@[reassoc (attr := simp)]
theorem section_comp_right (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ g = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.2
noncomputable def commonRetraction (f g : A ⟶ B) [IsCoreflexivePair f g] : B ⟶ A :=
  (IsCoreflexivePair.common_retraction f g).choose
@[reassoc (attr := simp)]
theorem left_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    f ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.1
@[reassoc (attr := simp)]
theorem right_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    g ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.2
theorem IsKernelPair.isReflexivePair {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : IsKernelPair q f g) :
    IsReflexivePair f g :=
  IsReflexivePair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2
theorem IsReflexivePair.swap [IsReflexivePair f g] : IsReflexivePair g f :=
  IsReflexivePair.mk' _ (section_comp_right f g) (section_comp_left f g)
theorem IsCoreflexivePair.swap [IsCoreflexivePair f g] : IsCoreflexivePair g f :=
  IsCoreflexivePair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
instance (B : D) :
    IsReflexivePair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  IsReflexivePair.mk' (F.map (adj.unit.app (G.obj B)))
    (by
      rw [← F.map_comp, adj.right_triangle_components]
      apply F.map_id)
    (adj.left_triangle_components _)
namespace Limits
variable (C)
class HasReflexiveCoequalizers : Prop where
  has_coeq : ∀ ⦃A B : C⦄ (f g : A ⟶ B) [IsReflexivePair f g], HasCoequalizer f g
class HasCoreflexiveEqualizers : Prop where
  has_eq : ∀ ⦃A B : C⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], HasEqualizer f g
attribute [instance 1] HasReflexiveCoequalizers.has_coeq
attribute [instance 1] HasCoreflexiveEqualizers.has_eq
theorem hasCoequalizer_of_common_section [HasReflexiveCoequalizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (rf : r ≫ f = 𝟙 _) (rg : r ≫ g = 𝟙 _) : HasCoequalizer f g := by
  letI := IsReflexivePair.mk' r rf rg
  infer_instance
theorem hasEqualizer_of_common_retraction [HasCoreflexiveEqualizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (fr : f ≫ r = 𝟙 _) (gr : g ≫ r = 𝟙 _) : HasEqualizer f g := by
  letI := IsCoreflexivePair.mk' r fr gr
  infer_instance
instance (priority := 100) hasReflexiveCoequalizers_of_hasCoequalizers [HasCoequalizers C] :
    HasReflexiveCoequalizers C where has_coeq A B f g _ := by infer_instance
instance (priority := 100) hasCoreflexiveEqualizers_of_hasEqualizers [HasEqualizers C] :
    HasCoreflexiveEqualizers C where has_eq A B f g _ := by infer_instance
end Limits
end CategoryTheory
namespace CategoryTheory
universe v v₂ u u₂
namespace Limits
inductive WalkingReflexivePair : Type where
  | zero
  | one
  deriving DecidableEq, Inhabited
open WalkingReflexivePair
namespace WalkingReflexivePair
inductive Hom : (WalkingReflexivePair → WalkingReflexivePair → Type)
  | left : Hom one zero
  | right : Hom one zero
  | reflexion : Hom zero one
  | leftCompReflexion : Hom one one
  | rightCompReflexion : Hom one one
  | id (X : WalkingReflexivePair) : Hom X X
  deriving DecidableEq
attribute [-simp, nolint simpNF] Hom.id.sizeOf_spec
attribute [-simp, nolint simpNF] Hom.leftCompReflexion.sizeOf_spec
attribute [-simp, nolint simpNF] Hom.rightCompReflexion.sizeOf_spec
def Hom.comp :
    ∀ { X Y Z : WalkingReflexivePair } (_ : Hom X Y)
      (_ : Hom Y Z), Hom X Z
  | _, _, _, id _, h => h
  | _, _, _, h, id _ => h
  | _, _, _, reflexion, left => id zero
  | _, _, _, reflexion, right => id zero
  | _, _, _, reflexion, rightCompReflexion => reflexion
  | _, _, _, reflexion, leftCompReflexion => reflexion
  | _, _, _, left, reflexion => leftCompReflexion
  | _, _, _, right, reflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, rightCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, leftCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, right => right
  | _, _, _, rightCompReflexion, left => right
  | _, _, _, leftCompReflexion, left => left
  | _, _, _, leftCompReflexion, right => left
  | _, _, _, leftCompReflexion, rightCompReflexion => leftCompReflexion
  | _, _, _, leftCompReflexion, leftCompReflexion => leftCompReflexion
instance category : SmallCategory WalkingReflexivePair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  comp_id := by intro _ _ f; cases f <;> rfl
  id_comp := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
open Hom
@[simp]
lemma Hom.id_eq (X : WalkingReflexivePair) :
    Hom.id X = 𝟙 X := by rfl
@[reassoc (attr := simp)]
lemma reflexion_comp_left : reflexion ≫ left = 𝟙 zero := rfl
@[reassoc (attr := simp)]
lemma reflexion_comp_right : reflexion ≫ right = 𝟙 zero := rfl
@[simp]
lemma leftCompReflexion_eq : leftCompReflexion = (left ≫ reflexion : one ⟶ one) := rfl
@[simp]
lemma rightCompReflexion_eq : rightCompReflexion = (right ≫ reflexion : one ⟶ one) := rfl
section FunctorsOutOfWalkingReflexivePair
variable {C : Type u} [Category.{v} C]
@[reassoc (attr := simp)]
lemma map_reflexion_comp_map_left (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map left = 𝟙 (F.obj zero) := by
  rw [← F.map_comp, reflexion_comp_left, F.map_id]
@[reassoc (attr := simp)]
lemma map_reflexion_comp_map_right (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map right = 𝟙 (F.obj zero) := by
  rw [← F.map_comp, reflexion_comp_right, F.map_id]
end FunctorsOutOfWalkingReflexivePair
end WalkingReflexivePair
namespace WalkingParallelPair
@[simps!]
def inclusionWalkingReflexivePair : WalkingParallelPair ⥤ WalkingReflexivePair where
  obj := fun x => match x with
    | one => WalkingReflexivePair.zero
    | zero => WalkingReflexivePair.one
  map := fun f => match f with
    | .left => WalkingReflexivePair.Hom.left
    | .right => WalkingReflexivePair.Hom.right
    | .id _ => WalkingReflexivePair.Hom.id _
  map_comp := by
    intro _ _ _ f g; cases f <;> cases g <;> rfl
variable {C : Type u} [Category.{v} C]
instance (X : WalkingReflexivePair) :
    Nonempty (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero => exact ⟨StructuredArrow.mk (Y := one) (𝟙 _)⟩
  | one => exact ⟨StructuredArrow.mk (Y := zero) (𝟙 _)⟩
open WalkingReflexivePair.Hom in
instance (X : WalkingReflexivePair) :
    IsConnected (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero =>
      refine IsConnected.of_induct  (j₀ := StructuredArrow.mk (Y := one) (𝟙 _)) ?_
      rintro p h₁ h₂ ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 h₁
      · exact h₁
  | one =>
      refine IsConnected.of_induct  (j₀ := StructuredArrow.mk (Y := zero) (𝟙 _))
        (fun p h₁ h₂ ↦ ?_)
      have hₗ : StructuredArrow.mk left ∈ p := (h₂ (StructuredArrow.homMk .left)).1 h₁
      have hᵣ : StructuredArrow.mk right ∈ p := (h₂ (StructuredArrow.homMk .right)).1 h₁
      rintro ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 hₗ
      · exact (h₂ (StructuredArrow.homMk .right)).2 hᵣ
      all_goals assumption
instance inclusionWalkingReflexivePair_final : Functor.Final inclusionWalkingReflexivePair where
  out := inferInstance
end WalkingParallelPair
end Limits
namespace Limits
open WalkingReflexivePair
variable {C : Type u} [Category.{v} C]
variable {A B : C}
def reflexivePair (f g : A ⟶ B) (s : B ⟶ A)
    (sl : s ≫ f = 𝟙 B := by aesop_cat) (sr : s ≫ g = 𝟙 B := by aesop_cat) :
    (WalkingReflexivePair ⥤ C) where
  obj x :=
    match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | .id _ => 𝟙 _
    | .left => f
    | .right => g
    | .reflexion => s
    | .rightCompReflexion => g ≫ s
    | .leftCompReflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
      simp only [Category.id_comp, Category.comp_id, Category.assoc, sl, sr,
        reassoc_of% sl, reassoc_of% sr] <;> rfl
section
variable {A B : C}
variable (f g : A ⟶ B) (s : B ⟶ A) {sl : s ≫ f = 𝟙 B} {sr : s ≫ g = 𝟙 B}
@[simp] lemma reflexivePair_obj_zero : (reflexivePair f g s sl sr).obj zero = B := rfl
@[simp] lemma reflexivePair_obj_one : (reflexivePair f g s sl sr).obj one = A := rfl
@[simp] lemma reflexivePair_map_right : (reflexivePair f g s sl sr).map .left = f := rfl
@[simp] lemma reflexivePair_map_left : (reflexivePair f g s sl sr).map .right = g := rfl
@[simp] lemma reflexivePair_map_reflexion : (reflexivePair f g s sl sr).map .reflexion = s := rfl
end
noncomputable def ofIsReflexivePair (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingReflexivePair ⥤ C := reflexivePair f g (commonSection f g)
@[simp]
lemma ofIsReflexivePair_map_left (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .left = f := rfl
@[simp]
lemma ofIsReflexivePair_map_right (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .right = g := rfl
noncomputable def inclusionWalkingReflexivePairOfIsReflexivePairIso
    (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingParallelPair.inclusionWalkingReflexivePair ⋙ (ofIsReflexivePair f g) ≅
      parallelPair f g :=
  diagramIsoParallelPair _
end Limits
namespace Limits
variable {C : Type u} [Category.{v} C]
namespace reflexivePair
open WalkingReflexivePair WalkingReflexivePair.Hom
section
section NatTrans
variable {F G : WalkingReflexivePair ⥤ C}
  (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
  (h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left := by aesop_cat)
  (h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right := by aesop_cat)
  (h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion := by aesop_cat)
def mkNatTrans : F ⟶ G where
  app := fun x ↦ match x with
    | zero => e₀
    | one => e₁
  naturality _ _ f := by
    cases f
    all_goals
      dsimp
      simp only [Functor.map_id, Category.id_comp, Category.comp_id,
        Functor.map_comp, h₁, h₂, h₃, reassoc_of% h₁, reassoc_of% h₂,
        reflexivePair_map_reflexion, reflexivePair_map_left, reflexivePair_map_right,
        Category.assoc]
@[simp]
lemma mkNatTrans_app_zero : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app zero = e₀ := rfl
@[simp]
lemma mkNatTrans_app_one : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app one = e₁ := rfl
end NatTrans
section NatIso
variable {F G : WalkingReflexivePair ⥤ C}
@[simps!]
def mkNatIso (e₀ : F.obj zero ≅ G.obj zero) (e₁ : F.obj one ≅ G.obj one)
    (h₁ : F.map left ≫ e₀.hom = e₁.hom ≫ G.map left := by aesop_cat)
    (h₂ : F.map right ≫ e₀.hom = e₁.hom ≫ G.map right := by aesop_cat)
    (h₃ : F.map reflexion ≫ e₁.hom = e₀.hom ≫ G.map reflexion := by aesop_cat) :
    F ≅ G where
  hom := mkNatTrans e₀.hom e₁.hom
  inv := mkNatTrans e₀.inv e₁.inv
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₁, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₂, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₀.hom, e₀.hom_inv_id_assoc, ← reassoc_of% h₃, e₁.hom_inv_id,
            Category.comp_id])
  hom_inv_id := by ext x; cases x <;> simp
  inv_hom_id := by ext x; cases x <;> simp
variable (F)
@[simps!]
def diagramIsoReflexivePair :
    F ≅ reflexivePair (F.map left) (F.map right) (F.map reflexion) :=
  mkNatIso (Iso.refl _) (Iso.refl _)
end NatIso
@[simps!]
def compRightIso {D : Type u₂} [Category.{v₂} D] {A B : C}
    (f g : A ⟶ B) (s : B ⟶ A) (sl : s ≫ f = 𝟙 B) (sr : s ≫ g = 𝟙 B) (F : C ⥤ D) :
    (reflexivePair f g s sl sr) ⋙ F ≅ reflexivePair (F.map f) (F.map g) (F.map s)
      (by simp only [← Functor.map_comp, sl, Functor.map_id])
      (by simp only [← Functor.map_comp, sr, Functor.map_id]) :=
  mkNatIso (Iso.refl _) (Iso.refl _)
lemma whiskerRightMkNatTrans {F G : WalkingReflexivePair ⥤ C}
    (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
    {h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left}
    {h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right}
    {h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion}
    {D : Type u₂} [Category.{v₂} D] (H : C ⥤ D) :
    whiskerRight (mkNatTrans e₀ e₁ : F ⟶ G) H =
      mkNatTrans (H.map e₀) (H.map e₁)
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₁])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₂])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₃]) := by
  ext x; cases x <;> simp
end
instance to_isReflexivePair {F : WalkingReflexivePair ⥤ C} :
    IsReflexivePair (F.map .left) (F.map .right) :=
  ⟨F.map .reflexion, map_reflexion_comp_map_left F, map_reflexion_comp_map_right F⟩
end reflexivePair
abbrev ReflexiveCofork (F : WalkingReflexivePair ⥤ C) := Cocone F
namespace ReflexiveCofork
open WalkingReflexivePair WalkingReflexivePair.Hom
variable {F : WalkingReflexivePair ⥤ C}
abbrev π (G : ReflexiveCofork F) : F.obj zero ⟶ G.pt := G.ι.app zero
@[simps pt]
def mk {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    ReflexiveCofork F where
  pt := X
  ι := reflexivePair.mkNatTrans π (F.map left ≫ π)
@[simp]
lemma mk_π {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    (mk π h).π = π := rfl
lemma condition (G : ReflexiveCofork F) : F.map left ≫ G.π = F.map right ≫ G.π := by
  rw [Cocone.w G left, Cocone.w G right]
@[simp]
lemma app_one_eq_π (G : ReflexiveCofork F) : G.ι.app zero = G.π := rfl
abbrev toCofork (G : ReflexiveCofork F) : Cofork (F.map left) (F.map right) :=
  Cofork.ofπ G.π (by simp)
end ReflexiveCofork
noncomputable section
open WalkingReflexivePair WalkingReflexivePair.Hom
variable (F : WalkingReflexivePair ⥤ C)
@[simps! functor_obj_pt inverse_obj_pt]
def reflexiveCoforkEquivCofork :
    ReflexiveCofork F ≌ Cofork (F.map left) (F.map right) :=
  (Functor.Final.coconesEquiv _ F).symm.trans (Cocones.precomposeEquivalence
    (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F))).symm
@[simp]
lemma reflexiveCoforkEquivCofork_functor_obj_π (G : ReflexiveCofork F) :
    ((reflexiveCoforkEquivCofork F).functor.obj G).π = G.π := by
  dsimp [reflexiveCoforkEquivCofork]
  rw [ReflexiveCofork.π, Cofork.π]
  aesop_cat
@[simp]
lemma reflexiveCoforkEquivCofork_inverse_obj_π
    (G : Cofork (F.map left) (F.map right)) :
    ((reflexiveCoforkEquivCofork F).inverse.obj G).π = G.π := by
  dsimp only [reflexiveCoforkEquivCofork, Equivalence.symm, Equivalence.trans,
    ReflexiveCofork.π, Cocones.precomposeEquivalence, Cocones.precompose,
    Functor.comp, Functor.Final.coconesEquiv]
  rw [Functor.Final.extendCocone_obj_ι_app' (Y := .one) (f := 𝟙 zero)]
  simp
def reflexiveCoforkEquivCoforkObjIso (G : ReflexiveCofork F) :
    (reflexiveCoforkEquivCofork F).functor.obj G ≅ G.toCofork :=
  Cofork.ext (Iso.refl _)
    (by simp [reflexiveCoforkEquivCofork, Cofork.π])
lemma hasReflexiveCoequalizer_iff_hasCoequalizer :
    HasColimit F ↔ HasCoequalizer (F.map left) (F.map right) := by
  simpa only [hasColimit_iff_hasInitial_cocone]
    using Equivalence.hasInitial_iff (reflexiveCoforkEquivCofork F)
instance reflexivePair_hasColimit_of_hasCoequalizer
    [h : HasCoequalizer (F.map left) (F.map right)] : HasColimit F :=
  hasReflexiveCoequalizer_iff_hasCoequalizer _|>.mpr h
def ReflexiveCofork.isColimitEquiv (G : ReflexiveCofork F) :
    IsColimit (G.toCofork) ≃ IsColimit G :=
  IsColimit.equivIsoColimit (reflexiveCoforkEquivCoforkObjIso F G).symm|>.trans <|
    (IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans <|
      Functor.Final.isColimitWhiskerEquiv _ _
section
variable [HasCoequalizer (F.map left) (F.map right)]
def reflexiveCoequalizerIsoCoequalizer :
    colimit F ≅ coequalizer (F.map left) (F.map right) :=
  ((ReflexiveCofork.isColimitEquiv _ _).symm (colimit.isColimit F)).coconePointUniqueUpToIso
    (colimit.isColimit _)
@[reassoc (attr := simp)]
lemma ι_reflexiveCoequalizerIsoCoequalizer_hom :
    colimit.ι F zero ≫ (reflexiveCoequalizerIsoCoequalizer F).hom =
      coequalizer.π (F.map left) (F.map right) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ReflexiveCofork.isColimitEquiv F _).symm _) _ WalkingParallelPair.one
@[reassoc (attr := simp)]
lemma π_reflexiveCoequalizerIsoCoequalizer_inv :
    coequalizer.π _ _ ≫ (reflexiveCoequalizerIsoCoequalizer F).inv = colimit.ι F _ := by
  rw [reflexiveCoequalizerIsoCoequalizer]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv, Cofork.ofπ_pt, colimit.cocone_x,
    Cofork.ofπ_ι_app, colimit.cocone_ι]
end
variable {A B : C} {f g : A ⟶ B} [IsReflexivePair f g] [h : HasCoequalizer f g]
instance ofIsReflexivePair_hasColimit_of_hasCoequalizer :
    HasColimit (ofIsReflexivePair f g) :=
  hasReflexiveCoequalizer_iff_hasCoequalizer _|>.mpr h
def colimitOfIsReflexivePairIsoCoequalizer :
    colimit (ofIsReflexivePair f g) ≅ coequalizer f g :=
  @reflexiveCoequalizerIsoCoequalizer _ _ (ofIsReflexivePair f g) h
@[reassoc (attr := simp)]
lemma ι_colimitOfIsReflexivePairIsoCoequalizer_hom :
    colimit.ι (ofIsReflexivePair f g) zero ≫ colimitOfIsReflexivePairIsoCoequalizer.hom =
      coequalizer.π f g := @ι_reflexiveCoequalizerIsoCoequalizer_hom _ _ _ h
@[reassoc (attr := simp)]
lemma π_colimitOfIsReflexivePairIsoCoequalizer_inv :
    coequalizer.π f g ≫ colimitOfIsReflexivePairIsoCoequalizer.inv =
      colimit.ι (ofIsReflexivePair f g) zero :=
  @π_reflexiveCoequalizerIsoCoequalizer_inv _ _ (ofIsReflexivePair f g) h
end
end Limits
namespace Limits
open WalkingReflexivePair
variable {C : Type u} [Category.{v} C]
theorem hasReflexiveCoequalizers_iff :
    HasColimitsOfShape WalkingReflexivePair C ↔ HasReflexiveCoequalizers C :=
  ⟨fun _ ↦ ⟨fun _ _ f g _ ↦ (hasReflexiveCoequalizer_iff_hasCoequalizer
      (reflexivePair f g (commonSection f g))).1 inferInstance⟩,
    fun _ ↦ ⟨inferInstance⟩⟩
end Limits
end CategoryTheory