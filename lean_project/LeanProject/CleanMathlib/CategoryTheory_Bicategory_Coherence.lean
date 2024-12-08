import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Bicategory.Free
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
open Quiver (Path)
open Quiver.Path
namespace CategoryTheory
open Bicategory Category
universe v u
namespace FreeBicategory
variable {B : Type u} [Quiver.{v + 1} B]
@[simp]
def inclusionPathAux {a : B} : ∀ {b : B}, Path a b → Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusionPathAux p).comp (Hom.of f)
local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b
def inclusionPath (a b : B) : Discrete (Path.{v + 1} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAux
def preinclusion (B : Type u) [Quiver.{v + 1} B] :
    PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) where
  obj a := a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η
@[simp]
theorem preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a :=
  rfl
@[simp]
theorem preinclusion_map₂ {a b : B} (f g : Discrete (Path.{v + 1} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom η))) := by
  rcases η with ⟨⟨⟩⟩
  cases Discrete.ext (by assumption)
  convert (inclusionPath a b).map_id _
@[simp]
def normalizeAux {a : B} : ∀ {b c : B}, Path a b → Hom b c → Path a c
  | _, _, p, Hom.of f => p.cons f
  | _, _, p, Hom.id _ => p
  | _, _, p, Hom.comp f g => normalizeAux (normalizeAux p f) g
@[simp]
def normalizeIso {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => Iso.refl _
  | _, _, _, Hom.id b => ρ_ _
  | _, _, p, Hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g
theorem normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAux p f = normalizeAux p g := by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funext; rfl
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom =
      (normalizeIso p f).hom ≫
        (preinclusion B).map₂ (eqToHom (Discrete.ext (normalizeAux_congr p η))) := by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, Bicategory.whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  | whisker_left _ _ ih =>
    dsimp
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  | whisker_right h η' ih =>
    dsimp
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih, comp_whiskerRight]
    have := dcongr_arg (fun x => (normalizeIso x h).hom) (normalizeAux_congr p (Quot.mk _ η'))
    dsimp at this; simp [this]
  | _ => simp
theorem normalizeAux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) :
    normalizeAux nil (f.comp g) = (normalizeAux nil f).comp (normalizeAux nil g) := by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]
def normalize (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (FreeBicategory B) (LocallyDiscrete (Paths B)) where
  obj a := ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
  map₂ η := eqToHom <| Discrete.ext <| normalizeAux_congr nil η
  mapId _ := eqToIso <| Discrete.ext rfl
  mapComp f g := eqToIso <| Discrete.ext <| normalizeAux_nil_comp f g
def normalizeUnitIso (a b : FreeBicategory B) :
    𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ @inclusionPath B _ a b :=
  NatIso.ofComponents (fun f => (λ_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v + 1} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1 
        injection ih with ih
        conv_rhs => rw [← ih]
        rfl))
instance locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b) := fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩
def inclusionMapCompAux {a b : B} :
    ∀ {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusionMapCompAux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _
def inclusion (B : Type u) [Quiver.{v + 1} B] :
    Pseudofunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) :=
  { 
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }
end FreeBicategory
end CategoryTheory