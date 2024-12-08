import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.Category.Quiv
noncomputable section
open CategoryTheory.Category
namespace CategoryTheory
universe uC' uD' uC uD
variable {C : Type uC} [Category.{uC'} C] (W : MorphismProperty C) {D : Type uD} [Category.{uD'} D]
namespace Localization
namespace Construction
structure LocQuiver (W : MorphismProperty C) where
  obj : C
instance : Quiver (LocQuiver W) where Hom A B := (A.obj ⟶ B.obj) ⊕ { f : B.obj ⟶ A.obj // W f }
def ιPaths (X : C) : Paths (LocQuiver W) :=
  ⟨X⟩
@[simp]
def ψ₁ {X Y : C} (f : X ⟶ Y) : ιPaths W X ⟶ ιPaths W Y :=
  Paths.of.map (Sum.inl f)
@[simp]
def ψ₂ {X Y : C} (w : X ⟶ Y) (hw : W w) : ιPaths W Y ⟶ ιPaths W X :=
  Paths.of.map (Sum.inr ⟨w, hw⟩)
inductive relations : HomRel (Paths (LocQuiver W))
  | id (X : C) : relations (ψ₁ W (𝟙 X)) (𝟙 _)
  | comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : relations (ψ₁ W (f ≫ g)) (ψ₁ W f ≫ ψ₁ W g)
  | Winv₁ {X Y : C} (w : X ⟶ Y) (hw : W w) : relations (ψ₁ W w ≫ ψ₂ W w hw) (𝟙 _)
  | Winv₂ {X Y : C} (w : X ⟶ Y) (hw : W w) : relations (ψ₂ W w hw ≫ ψ₁ W w) (𝟙 _)
end Construction
end Localization
namespace MorphismProperty
open Localization.Construction
def Localization :=
  CategoryTheory.Quotient (Localization.Construction.relations W)
instance : Category (Localization W) := by
  dsimp only [Localization]
  infer_instance
def Q : C ⥤ W.Localization where
  obj X := (Quotient.functor _).obj (Paths.of.obj ⟨X⟩)
  map f := (Quotient.functor _).map (ψ₁ W f)
  map_id X := Quotient.sound _ (relations.id X)
  map_comp f g := Quotient.sound _ (relations.comp f g)
end MorphismProperty
namespace Localization
namespace Construction
variable {W}
def wIso {X Y : C} (w : X ⟶ Y) (hw : W w) : Iso (W.Q.obj X) (W.Q.obj Y) where
  hom := W.Q.map w
  inv := (Quotient.functor _).map (by dsimp; exact Paths.of.map (Sum.inr ⟨w, hw⟩))
  hom_inv_id := Quotient.sound _ (relations.Winv₁ w hw)
  inv_hom_id := Quotient.sound _ (relations.Winv₂ w hw)
abbrev wInv {X Y : C} (w : X ⟶ Y) (hw : W w) :=
  (wIso w hw).inv
variable (W)
theorem _root_.CategoryTheory.MorphismProperty.Q_inverts : W.IsInvertedBy W.Q := fun _ _ w hw =>
  (Localization.Construction.wIso w hw).isIso_hom
variable {W}
variable (G : C ⥤ D) (hG : W.IsInvertedBy G)
@[simps!]
def liftToPathCategory : Paths (LocQuiver W) ⥤ D :=
  Quiv.lift
    { obj := fun X => G.obj X.obj
      map := by
        intros X Y
        rintro (f | ⟨g, hg⟩)
        · exact G.map f
        · haveI := hG g hg
          exact inv (G.map g) }
@[simps!]
def lift : W.Localization ⥤ D :=
  Quotient.lift (relations W) (liftToPathCategory G hG)
    (by
      rintro ⟨X⟩ ⟨Y⟩ f₁ f₂ r
      rcases r with (_|_|⟨f,hf⟩|⟨f,hf⟩)
      · aesop_cat
      · aesop_cat
      all_goals
        dsimp
        haveI := hG f hf
        simp
        rfl)
@[simp]
theorem fac : W.Q ⋙ lift G hG = G :=
  Functor.ext (fun _ => rfl)
    (by
      intro X Y f
      simp only [Functor.comp_map, eqToHom_refl, comp_id, id_comp]
      dsimp [MorphismProperty.Q, Quot.liftOn, Quotient.functor]
      rw [composePath_toPath])
theorem uniq (G₁ G₂ : W.Localization ⥤ D) (h : W.Q ⋙ G₁ = W.Q ⋙ G₂) : G₁ = G₂ := by
  suffices h' : Quotient.functor _ ⋙ G₁ = Quotient.functor _ ⋙ G₂ by
    refine Functor.ext ?_ ?_
    · rintro ⟨⟨X⟩⟩
      apply Functor.congr_obj h
    · rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ ⟨f⟩
      apply Functor.congr_hom h'
  refine Paths.ext_functor ?_ ?_
  · ext X
    cases X
    apply Functor.congr_obj h
  · rintro ⟨X⟩ ⟨Y⟩ (f | ⟨w, hw⟩)
    · simpa only using Functor.congr_hom h f
    · have hw : W.Q.map w = (wIso w hw).hom := rfl
      have hw' := Functor.congr_hom h w
      simp only [Functor.comp_map, hw] at hw'
      refine Functor.congr_inv_of_congr_hom _ _ _ ?_ ?_ hw'
      all_goals apply Functor.congr_obj h
variable (W)
@[simps]
def objEquiv : C ≃ W.Localization where
  toFun := W.Q.obj
  invFun X := X.as.obj
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨X⟩⟩
    rfl
variable {W}
theorem morphismProperty_is_top (P : MorphismProperty W.Localization)
    [P.IsStableUnderComposition] (hP₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P (W.Q.map f))
    (hP₂ : ∀ ⦃X Y : C⦄ (w : X ⟶ Y) (hw : W w), P (wInv w hw)) :
    P = ⊤ := by
  funext X Y f
  ext
  constructor
  · intro
    apply MorphismProperty.top_apply
  · intro
    let G : _ ⥤ W.Localization := Quotient.functor _
    haveI : G.Full := Quotient.full_functor _
    suffices ∀ (X₁ X₂ : Paths (LocQuiver W)) (f : X₁ ⟶ X₂), P (G.map f) by
      rcases X with ⟨⟨X⟩⟩
      rcases Y with ⟨⟨Y⟩⟩
      simpa only [Functor.map_preimage] using this _ _ (G.preimage f)
    intros X₁ X₂ p
    induction' p with X₂ X₃ p g hp
    · simpa only [Functor.map_id] using hP₁ (𝟙 X₁.obj)
    · let p' : X₁ ⟶X₂ := p
      rw [show p'.cons g = p' ≫ Quiver.Hom.toPath g by rfl, G.map_comp]
      refine P.comp_mem _ _ hp ?_
      rcases g with (g | ⟨g, hg⟩)
      · apply hP₁
      · apply hP₂
theorem morphismProperty_is_top' (P : MorphismProperty W.Localization)
    [P.IsStableUnderComposition] (hP₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P (W.Q.map f))
    (hP₂ : ∀ ⦃X Y : W.Localization⦄ (e : X ≅ Y) (_ : P e.hom), P e.inv) : P = ⊤ :=
  morphismProperty_is_top P hP₁ (fun _ _ w _ => hP₂ _ (hP₁ w))
namespace NatTransExtension
variable {F₁ F₂ : W.Localization ⥤ D} (τ : W.Q ⋙ F₁ ⟶ W.Q ⋙ F₂)
def app (X : W.Localization) : F₁.obj X ⟶ F₂.obj X :=
  eqToHom (congr_arg F₁.obj ((objEquiv W).right_inv X).symm) ≫
    τ.app ((objEquiv W).invFun X) ≫ eqToHom (congr_arg F₂.obj ((objEquiv W).right_inv X))
@[simp]
theorem app_eq (X : C) : (app τ) (W.Q.obj X) = τ.app X := by
  simp only [app, eqToHom_refl, comp_id, id_comp]
  rfl
end NatTransExtension
@[simps]
def natTransExtension {F₁ F₂ : W.Localization ⥤ D} (τ : W.Q ⋙ F₁ ⟶ W.Q ⋙ F₂) : F₁ ⟶ F₂ where
  app := NatTransExtension.app τ
  naturality := by
    suffices MorphismProperty.naturalityProperty (NatTransExtension.app τ) = ⊤ by
      intro X Y f
      simpa only [← this] using MorphismProperty.top_apply f
    refine morphismProperty_is_top'
      (MorphismProperty.naturalityProperty (NatTransExtension.app τ))
      ?_ (MorphismProperty.naturalityProperty.stableUnderInverse _)
    intros X Y f
    dsimp
    simpa only [NatTransExtension.app_eq] using τ.naturality f
@[simp]
theorem natTransExtension_hcomp {F G : W.Localization ⥤ D} (τ : W.Q ⋙ F ⟶ W.Q ⋙ G) :
    𝟙 W.Q ◫ natTransExtension τ = τ := by aesop_cat
theorem natTrans_hcomp_injective {F G : W.Localization ⥤ D} {τ₁ τ₂ : F ⟶ G}
    (h : 𝟙 W.Q ◫ τ₁ = 𝟙 W.Q ◫ τ₂) : τ₁ = τ₂ := by
  ext X
  have eq := (objEquiv W).right_inv X
  simp only [objEquiv] at eq
  rw [← eq, ← NatTrans.id_hcomp_app, ← NatTrans.id_hcomp_app, h]
variable (W D)
namespace WhiskeringLeftEquivalence
@[simps!]
def functor : (W.Localization ⥤ D) ⥤ W.FunctorsInverting D :=
  FullSubcategory.lift _ ((whiskeringLeft _ _ D).obj W.Q) fun _ =>
    MorphismProperty.IsInvertedBy.of_comp W W.Q W.Q_inverts _
@[simps!]
def inverse : W.FunctorsInverting D ⥤ W.Localization ⥤ D where
  obj G := lift G.obj G.property
  map τ := natTransExtension (eqToHom (by rw [fac]) ≫ τ ≫ eqToHom (by rw [fac]))
  map_id G :=
    natTrans_hcomp_injective
      (by
        rw [natTransExtension_hcomp]
        ext X
        simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, comp_id, id_comp,
          NatTrans.hcomp_id_app, NatTrans.id_app, Functor.map_id]
        rfl)
  map_comp τ₁ τ₂ :=
    natTrans_hcomp_injective
      (by
        ext X
        simp only [natTransExtension_hcomp, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
          id_comp, comp_id, NatTrans.hcomp_app, NatTrans.id_app, Functor.map_id,
          natTransExtension_app, NatTransExtension.app_eq]
        rfl)
@[simps!]
def unitIso : 𝟭 (W.Localization ⥤ D) ≅ functor W D ⋙ inverse W D :=
  eqToIso
    (by
      refine Functor.ext (fun G => ?_) fun G₁ G₂ τ => ?_
      · apply uniq
        dsimp [Functor]
        erw [fac]
        rfl
      · apply natTrans_hcomp_injective
        ext X
        simp)
@[simps!]
def counitIso : inverse W D ⋙ functor W D ≅ 𝟭 (W.FunctorsInverting D) :=
  eqToIso
    (by
      refine Functor.ext ?_ ?_
      · rintro ⟨G, hG⟩
        ext
        exact fac G hG
      · rintro ⟨G₁, hG₁⟩ ⟨G₂, hG₂⟩ f
        ext
        apply NatTransExtension.app_eq)
end WhiskeringLeftEquivalence
def whiskeringLeftEquivalence : W.Localization ⥤ D ≌ W.FunctorsInverting D where
  functor := WhiskeringLeftEquivalence.functor W D
  inverse := WhiskeringLeftEquivalence.inverse W D
  unitIso := WhiskeringLeftEquivalence.unitIso W D
  counitIso := WhiskeringLeftEquivalence.counitIso W D
  functor_unitIso_comp F := by
    ext
    simp only [WhiskeringLeftEquivalence.unitIso_hom, eqToHom_app, eqToHom_refl,
      WhiskeringLeftEquivalence.counitIso_hom, eqToHom_map, eqToHom_trans]
    rfl
end Construction
end Localization
end CategoryTheory