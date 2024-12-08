import Mathlib.CategoryTheory.Monoidal.Types.Symmetric
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.Tactic.ApplyFun
universe w w' v v' u₁ u₂ u₃
noncomputable section
namespace CategoryTheory
open Opposite
open MonoidalCategory
variable (V : Type v) [Category.{w} V] [MonoidalCategory V]
class EnrichedCategory (C : Type u₁) where
  Hom : C → C → V
  id (X : C) : 𝟙_ V ⟶ Hom X X
  comp (X Y Z : C) : Hom X Y ⊗ Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (λ_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _ := by aesop_cat
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _ := by aesop_cat
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z =
    _ ◁ comp X Y Z ≫ comp W X Z := by aesop_cat
notation X " ⟶[" V "] " Y:10 => (EnrichedCategory.Hom X Y : V)
variable {C : Type u₁} [EnrichedCategory V C]
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X
def eComp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z
@[reassoc (attr := simp)]
theorem e_id_comp (X Y : C) :
    (λ_ (X ⟶[V] Y)).inv ≫ eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y
@[reassoc (attr := simp)]
theorem e_comp_id (X Y : C) :
    (ρ_ (X ⟶[V] Y)).inv ≫ _ ◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y
@[reassoc (attr := simp)]
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ eComp V W X Y ▷ _ ≫ eComp V W Y Z =
      _ ◁ eComp V X Y Z ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z
@[reassoc]
theorem e_assoc' (W X Y Z : C) :
    (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X Z =
      eComp V W X Y ▷ _ ≫ eComp V W Y Z := by
  rw [← e_assoc V W X Y Z, Iso.hom_inv_id_assoc]
section
variable {V} {W : Type v'} [Category.{w'} W] [MonoidalCategory W]
@[nolint unusedArguments]
def TransportEnrichment (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁) :=
  C
variable (F : V ⥤ W) [F.LaxMonoidal]
open Functor.LaxMonoidal
instance : EnrichedCategory W (TransportEnrichment F C) where
  Hom := fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => ε F ≫ F.map (eId V X)
  comp := fun X Y Z : C => μ F _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    simp only [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert F.map_id _
    simp
  comp_id X Y := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc,
      Functor.LaxMonoidal.right_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert F.map_id _
    simp
  assoc P Q R S := by
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      ← associativity_inv_assoc, ← F.map_comp, ← F.map_comp, e_assoc,
      F.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc]
end
def categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C] :
    Category.{v} C where
  Hom := 𝒞.Hom
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := congr_fun (e_id_comp (Type v) _ _) f
  comp_id f := congr_fun (e_comp_id (Type v) _ _) f
  assoc f g h := (congr_fun (e_assoc (Type v) _ _ _ _) ⟨f, g, h⟩ : _)
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] :
    EnrichedCategory (Type v) C where
  Hom := 𝒞.Hom
  id X _ := 𝟙 X
  comp _ _ _ p := p.1 ≫ p.2
  id_comp X Y := by ext; simp
  comp_id X Y := by ext; simp
  assoc W X Y Z := by ext ⟨f, g, h⟩; simp
def enrichedCategoryTypeEquivCategory (C : Type u₁) :
    EnrichedCategory (Type v) C ≃ Category.{v} C where
  toFun _ := categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C
  left_inv _ := rfl
  right_inv _ := rfl
section
variable {W : Type v} [Category.{w} W] [MonoidalCategory W] [EnrichedCategory W C]
@[nolint unusedArguments]
def ForgetEnrichment (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C
variable (W)
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X
def ForgetEnrichment.to (X : ForgetEnrichment W C) : C :=
  X
@[simp]
theorem ForgetEnrichment.to_of (X : C) : ForgetEnrichment.to W (ForgetEnrichment.of W X) = X :=
  rfl
@[simp]
theorem ForgetEnrichment.of_to (X : ForgetEnrichment W C) :
    ForgetEnrichment.of W (ForgetEnrichment.to W X) = X :=
  rfl
instance categoryForgetEnrichment : Category (ForgetEnrichment W C) :=
  enrichedCategoryTypeEquivCategory C (inferInstanceAs (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f
def ForgetEnrichment.homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y :=
  f
@[simp]
theorem ForgetEnrichment.homTo_homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.homTo W (ForgetEnrichment.homOf W f) = f :=
  rfl
@[simp]
theorem ForgetEnrichment.homOf_homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    ForgetEnrichment.homOf W (ForgetEnrichment.homTo W f) = f :=
  rfl
@[simp]
theorem forgetEnrichment_id (X : ForgetEnrichment W C) :
    ForgetEnrichment.homTo W (𝟙 X) = eId W (ForgetEnrichment.to W X : C) :=
  Category.id_comp _
@[simp]
theorem forgetEnrichment_id' (X : C) :
    ForgetEnrichment.homOf W (eId W X) = 𝟙 (ForgetEnrichment.of W X : C) :=
  (forgetEnrichment_id W (ForgetEnrichment.of W X)).symm
@[simp]
theorem forgetEnrichment_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ForgetEnrichment.homTo W (f ≫ g) =
      ((λ_ (𝟙_ W)).inv ≫ (ForgetEnrichment.homTo W f ⊗ ForgetEnrichment.homTo W g)) ≫
        eComp W _ _ _ :=
  rfl
end
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  obj : C → D
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id : ∀ X : C, eId V X ≫ map X X = eId V (obj X) := by aesop_cat
  map_comp :
    ∀ X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    aesop_cat
attribute [reassoc (attr := simp)] EnrichedFunctor.map_id
attribute [reassoc (attr := simp)] EnrichedFunctor.map_comp
@[simps]
def EnrichedFunctor.id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where
  obj X := X
  map _ _ := 𝟙 _
instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩
@[simps]
def EnrichedFunctor.comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E where
  obj X := G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _
section
variable {W : Type (v + 1)} [Category.{v} W] [MonoidalCategory W]
def EnrichedFunctor.forget {C : Type u₁} {D : Type u₂} [EnrichedCategory W C] [EnrichedCategory W D]
    (F : EnrichedFunctor W C D) : ForgetEnrichment W C ⥤ ForgetEnrichment W D where
  obj X := ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    dsimp
    apply_fun ForgetEnrichment.homTo W
    · simp only [Iso.cancel_iso_inv_left, Category.assoc, tensor_comp,
        ForgetEnrichment.homTo_homOf, EnrichedFunctor.map_comp, forgetEnrichment_comp]
      rfl
    · intro f g w; apply_fun ForgetEnrichment.homOf W at w; simpa using w
end
section
variable {V}
variable {D : Type u₂} [EnrichedCategory V D]
@[ext]
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  naturality :
    ∀ X Y : C,
      (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ app Y) ≫ eComp V _ _ _ =
        (app X ⊗ G.map X Y) ≫ eComp V _ _ _
variable [BraidedCategory V]
open BraidedCategory
@[simps]
def enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type max u₁ w where
  obj A := GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f σ :=
    { app := fun X => f.unop ≫ σ.app X
      naturality := fun X Y => by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, Category.assoc,
          Category.assoc, ← braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p, ←
          tensor_comp_assoc, Category.id_comp] }
end
section
attribute [local instance] categoryOfEnrichedCategoryType
@[simps]
def enrichedFunctorTypeEquivFunctor {C : Type u₁} [𝒞 : EnrichedCategory (Type v) C] {D : Type u₂}
    [𝒟 : EnrichedCategory (Type v) D] : EnrichedFunctor (Type v) C D ≃ C ⥤ D where
  toFun F :=
    { obj := fun X => F.obj X
      map := fun f => F.map _ _ f
      map_id := fun X => congr_fun (F.map_id X) PUnit.unit
      map_comp := fun f g => congr_fun (F.map_comp _ _ _) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun _ _ f => F.map f
      map_id := fun X => by ext ⟨⟩; exact F.map_id X
      map_comp := fun X Y Z => by ext ⟨f, g⟩; exact F.map_comp f g }
  left_inv _ := rfl
  right_inv _ := rfl
def enrichedNatTransYonedaTypeIsoYonedaNatTrans {C : Type v} [EnrichedCategory (Type v) C]
    {D : Type v} [EnrichedCategory (Type v) D] (F G : EnrichedFunctor (Type v) C D) :
    enrichedNatTransYoneda F G ≅
      yoneda.obj (enrichedFunctorTypeEquivFunctor F ⟶ enrichedFunctorTypeEquivFunctor G) :=
  NatIso.ofComponents
    (fun α =>
      { hom := fun σ x =>
          { app := fun X => σ.app X x
            naturality := fun X Y f => congr_fun (σ.naturality X Y) ⟨x, f⟩ }
        inv := fun σ =>
          { app := fun X x => (σ x).app X
            naturality := fun X Y => by ext ⟨x, f⟩; exact (σ x).naturality f } })
    (by aesop_cat)
end
end CategoryTheory