import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.CategoryTheory.DiscreteCategory
universe u
namespace CategoryTheory
open MonoidalCategory
namespace FreeMonoidalCategory
variable {C : Type u}
section
variable (C)
inductive NormalMonoidalObject : Type u
  | unit : NormalMonoidalObject
  | tensor : NormalMonoidalObject → C → NormalMonoidalObject
end
local notation "F" => FreeMonoidalCategory
local notation "N" => Discrete ∘ NormalMonoidalObject
local infixr:10 " ⟶ᵐ " => Hom
instance (x y : N C) : Subsingleton (x ⟶ y) := Discrete.instSubsingletonDiscreteHom _ _
@[simp]
def inclusionObj : NormalMonoidalObject C → F C
  | NormalMonoidalObject.unit => unit
  | NormalMonoidalObject.tensor n a => tensor (inclusionObj n) (of a)
def inclusion : N C ⥤ F C :=
  Discrete.functor inclusionObj
@[simp]
theorem inclusion_obj (X : N C) :
    inclusion.obj X = inclusionObj X.as :=
  rfl
@[simp]
theorem inclusion_map {X Y : N C} (f : X ⟶ Y) :
    inclusion.map f = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom f))) := by
  rcases f with ⟨⟨⟩⟩
  cases Discrete.ext (by assumption)
  apply inclusion.map_id
def normalizeObj : F C → NormalMonoidalObject C → NormalMonoidalObject C
  | unit, n => n
  | of X, n => NormalMonoidalObject.tensor n X
  | tensor X Y, n => normalizeObj Y (normalizeObj X n)
@[simp]
theorem normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C)) n = n :=
  rfl
@[simp]
theorem normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeObj (X ⊗ Y) n = normalizeObj Y (normalizeObj X n) :=
  rfl
def normalizeObj' (X : F C) : N C ⥤ N C := Discrete.functor fun n ↦ ⟨normalizeObj X n⟩
section
open Hom
@[simp]
def normalizeMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (normalizeObj' X ⟶ normalizeObj' Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, (@comp _ _ _ _ f g) => normalizeMapAux f ≫ normalizeMapAux g
  | _, _, (@Hom.tensor _ T _ _ W f g) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux g).app ⟨normalizeObj T X⟩ ≫
      (normalizeObj' W).map ((normalizeMapAux f).app ⟨X⟩)
  | _, _, (@Hom.whiskerLeft _ T _ W f) =>
    Discrete.natTrans <| fun ⟨X⟩ => (normalizeMapAux f).app ⟨normalizeObj T X⟩
  | _, _, (@Hom.whiskerRight _ T _ f W) =>
    Discrete.natTrans <| fun X => (normalizeObj' W).map <| (normalizeMapAux f).app X
end
section
variable (C)
@[simp]
def normalize : F C ⥤ N C ⥤ N C where
  obj X := normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by aesop_cat)
@[simp]
def normalize' : F C ⥤ N C ⥤ F C :=
  normalize C ⋙ (whiskeringRight _ _ _).obj inclusion
def fullNormalize : F C ⥤ N C where
  obj X := ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩
@[simp]
def tensorFunc : F C ⥤ N C ⥤ F C where
  obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ ⊗ X
  map f := Discrete.natTrans (fun _ => _ ◁ f)
theorem tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).app n = _ ◁ f :=
  rfl
theorem tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C).obj Z).map f = inclusion.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp
@[simp]
def normalizeIsoApp :
    ∀ (X : F C) (n : N C), ((tensorFunc C).obj X).obj n ≅ ((normalize' C).obj X).obj n
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp X n) a ≪≫ normalizeIsoApp _ _
@[simp]
def normalizeIsoApp' :
    ∀ (X : F C) (n : NormalMonoidalObject C), inclusionObj n ⊗ X ≅ inclusionObj (normalizeObj X n)
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X Y, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' X n) Y ≪≫ normalizeIsoApp' _ _
theorem normalizeIsoApp_eq :
    ∀ (X : F C) (n : N C), normalizeIsoApp C X n = normalizeIsoApp' C X n.as
  | of _, _ => rfl
  | unit, _ => rfl
  | tensor X Y, n => by
      rw [normalizeIsoApp, normalizeIsoApp']
      rw [normalizeIsoApp_eq X n]
      rw [normalizeIsoApp_eq Y ⟨normalizeObj X n.as⟩]
      rfl
@[simp]
theorem normalizeIsoApp_tensor (X Y : F C) (n : N C) :
    normalizeIsoApp C (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C X n) Y ≪≫ normalizeIsoApp _ _ _ :=
  rfl
@[simp]
theorem normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _ :=
  rfl
@[simp]
def normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X :=
  NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)
section
variable {C}
theorem normalizeObj_congr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    normalizeObj X n = normalizeObj Y n := by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft  _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl
theorem normalize_naturality (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    inclusionObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom =
      (normalizeIsoApp' C X n).hom ≫
        inclusion.map (eqToHom (Discrete.ext (normalizeObj_congr n f))) := by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp', tensor_eq_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp', tensor_eq_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp
end
set_option tactic.skipAssignedInstances false in
def normalizeIso : tensorFunc C ≅ normalize' C :=
  NatIso.ofComponents (normalizeIsoAux C) <| by
    intro X Y f
    ext ⟨n⟩
    convert normalize_naturality n f using 1
    any_goals dsimp [NatIso.ofComponents]; congr; apply normalizeIsoApp_eq
def fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion :=
  NatIso.ofComponents
  (fun X => (λ_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc, Category.assoc, Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))
end
instance subsingleton_hom : Quiver.IsThin (F C) := fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩
section Groupoid
section
open Hom
def inverseAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
  | _, _, Hom.id X => id X
  | _, _, α_hom _ _ _ => α_inv _ _ _
  | _, _, α_inv _ _ _ => α_hom _ _ _
  | _, _, ρ_hom _ => ρ_inv _
  | _, _, ρ_inv _ => ρ_hom _
  | _, _, l_hom _ => l_inv _
  | _, _, l_inv _ => l_hom _
  | _, _, comp f g => (inverseAux g).comp (inverseAux f)
  | _, _, Hom.whiskerLeft X f => (inverseAux f).whiskerLeft X
  | _, _, Hom.whiskerRight f X => (inverseAux f).whiskerRight X
  | _, _, Hom.tensor f g => (inverseAux f).tensor (inverseAux g)
end
instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by aesop_cat) }
end Groupoid
end FreeMonoidalCategory
end CategoryTheory