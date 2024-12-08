import Mathlib.CategoryTheory.Localization.Construction
noncomputable section
namespace CategoryTheory
open Category
variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category E]
namespace Functor
class IsLocalization : Prop where
  inverts : W.IsInvertedBy L
  isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)
instance q_isLocalization : W.Q.IsLocalization W where
  inverts := W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl
end Functor
namespace Localization
structure StrictUniversalPropertyFixedTarget where
  inverts : W.IsInvertedBy L
  lift : ∀ (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  uniq : ∀ (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂
@[simps]
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.Q W E where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq
instance : Inhabited (StrictUniversalPropertyFixedTarget W.Q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩
@[simps]
def strictUniversalPropertyFixedTargetId (hW : W ≤ MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E where
  inverts _ _ f hf := hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq
end Localization
namespace Functor
theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }
theorem IsLocalization.for_id (hW : W ≤ MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)
end Functor
namespace Localization
variable [L.IsLocalization W]
theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts
@[simps! hom]
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)
@[reassoc (attr := simp)]
lemma isoOfHom_hom_inv_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    L.map f ≫ (isoOfHom L W f hf).inv = 𝟙 _ :=
  (isoOfHom L W f hf).hom_inv_id
@[reassoc (attr := simp)]
lemma isoOfHom_inv_hom_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _ :=
  (isoOfHom L W f hf).inv_hom_id
@[simp]
lemma isoOfHom_id_inv (X : C) (hX : W (𝟙 X)) :
    (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _ := by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom, Iso.inv_hom_id, id_comp,
    isoOfHom_hom, Functor.map_id]
variable {W}
lemma Construction.wIso_eq_isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wIso f hf = isoOfHom W.Q W f hf := by ext; rfl
lemma Construction.wInv_eq_isoOfHom_inv {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wInv f hf = (isoOfHom W.Q W f hf).inv :=
  congr_arg Iso.inv (wIso_eq_isoOfHom f hf)
instance : (Localization.Construction.lift L (inverts L W)).IsEquivalence :=
  (inferInstance : L.IsLocalization W).isEquivalence
variable (W)
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence
def qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L :=
  eqToIso (Construction.fac _ _)
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (Functor.associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := Functor.rightUnitor _
theorem essSurj (W) [L.IsLocalization W] : L.EssSurj :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  FullSubcategory.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))
instance : (whiskeringLeftFunctor L W E).IsEquivalence := by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        erw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app, eqToHom_refl,
          eqToHom_refl, comp_id, id_comp]
        · rfl
        all_goals
          change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ _ = L ⋙ _
          rw [Construction.fac])
  exact Functor.isEquivalence_of_iso iso
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence
@[nolint unusedArguments]
def whiskeringLeftFunctor' [L.IsLocalization W] (E : Type*) [Category E] :
    (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L
theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl
variable {E} in
@[simp]
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl
instance : (whiskeringLeftFunctor' L W E).Full := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full 
instance : (whiskeringLeftFunctor' L W E).Faithful := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful 
lemma full_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category E] :
    ((whiskeringLeft C D E).obj L).Full :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Full
lemma faithful_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category E] :
    ((whiskeringLeft C D E).obj L).Faithful :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful
variable {E}
theorem natTrans_ext (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
    (h : ∀ X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' := by
  haveI := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom), τ.naturality, τ'.naturality, h]
class Lifting (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E) where
  iso' : L ⋙ F' ≅ F
def Lifting.iso (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F'] :
    L ⋙ F' ≅ F :=
  Lifting.iso' W
variable {W}
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩
instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso L W F _
instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.Q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩
variable (W)
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)
@[simp]
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X
@[reassoc (attr := simp)]
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  natTrans_ext L W _ _ fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]
@[simp]
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  natTrans_ext L W _ _ fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl
@[simps]
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv
namespace Lifting
@[simps]
instance compRight {E' : Type*} [Category E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩
@[simps]
instance id : Lifting L W L (𝟭 D) :=
  ⟨Functor.rightUnitor L⟩
@[simps]
instance compLeft (F : D ⥤ E) : Localization.Lifting L W (L ⋙ F) F := ⟨Iso.refl _⟩
@[simp]
lemma compLeft_iso (W) (F : D ⥤ E) : Localization.Lifting.iso L W (L ⋙ F) F = Iso.refl _ := rfl
@[simps]
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩
end Lifting
end Localization
namespace Functor
namespace IsLocalization
open Localization
theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W := by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }
theorem of_equivalence_target {E : Type*} [Category E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization W := by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }
instance (F : D ⥤ E) [F.IsEquivalence] [L.IsLocalization W] :
    (L ⋙ F).IsLocalization W :=
  of_equivalence_target L W _ F.asEquivalence (Iso.refl _)
lemma of_isEquivalence (L : C ⥤ D) (W : MorphismProperty C)
    (hW : W ≤ MorphismProperty.isomorphisms C) [IsEquivalence L] :
    L.IsLocalization W := by
  haveI : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor
end IsLocalization
end Functor
namespace Localization
variable {D₁ D₂ : Type _} [Category D₁] [Category D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']
def uniq : D₁ ≌ D₂ :=
  (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')
lemma uniq_symm : (uniq L₁ L₂ W').symm = uniq L₂ L₁ W' := rfl
def compUniqFunctor : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂ :=
  calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (Functor.associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'
def compUniqInverse : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁ := compUniqFunctor L₂ L₁ W'
instance : Lifting L₁ W' L₂ (uniq L₁ L₂ W').functor := ⟨compUniqFunctor L₁ L₂ W'⟩
instance : Lifting L₂ W' L₁ (uniq L₁ L₂ W').inverse := ⟨compUniqInverse L₁ L₂ W'⟩
def isoUniqFunctor (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂) :
    F ≅ (uniq L₁ L₂ W').functor :=
  letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)
end Localization
section
variable {X Y : C} (f g : X ⟶ Y)
def AreEqualizedByLocalization : Prop := W.Q.map f = W.Q.map g
lemma areEqualizedByLocalization_iff [L.IsLocalization W] :
    AreEqualizedByLocalization W f g ↔ L.map f = L.map g := by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]
namespace AreEqualizedByLocalization
lemma mk (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g) :
    AreEqualizedByLocalization W f g :=
  (areEqualizedByLocalization_iff L W f g).2 h
variable {W f g}
lemma map_eq (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] :
    L.map f = L.map g :=
  (areEqualizedByLocalization_iff L W f g).1 h
end AreEqualizedByLocalization
end
end CategoryTheory