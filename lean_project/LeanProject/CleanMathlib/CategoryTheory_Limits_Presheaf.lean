import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Over
namespace CategoryTheory
open Category Limits
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace Presheaf
variable {C : Type u₁} [Category.{v₁} C]
variable {ℰ : Type u₂} [Category.{v₁} ℰ] (A : C ⥤ ℰ)
@[simps!]
def restrictedYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type v₁ :=
  yoneda ⋙ (whiskeringLeft _ _ (Type v₁)).obj (Functor.op A)
def restrictedYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type v₁) (E : ℰ) :
    (CostructuredArrow.proj yoneda P ⋙ A ⟶
      (Functor.const (CostructuredArrow yoneda P)).obj E) ≃
      (P ⟶ (restrictedYoneda A).obj E) where
  toFun f :=
    { app := fun _ x => f.app (CostructuredArrow.mk (yonedaEquiv.symm x))
      naturality := fun {X₁ X₂} φ => by
        ext x
        let ψ : CostructuredArrow.mk (yonedaEquiv.symm (P.toPrefunctor.map φ x)) ⟶
          CostructuredArrow.mk (yonedaEquiv.symm x) := CostructuredArrow.homMk φ.unop (by
            dsimp [yonedaEquiv]
            aesop_cat )
        simpa using (f.naturality ψ).symm }
  invFun g :=
    { app := fun y => yonedaEquiv (y.hom ≫ g)
      naturality := fun {X₁ X₂} φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        dsimp [yonedaEquiv]
        simp only [comp_id, id_comp]
        refine (congr_fun (g.naturality φ.left.op) (X₂.hom.app (Opposite.op X₂.left)
          (𝟙 _))).symm.trans ?_
        dsimp
        apply congr_arg
        simpa using congr_fun (X₂.hom.naturality φ.left.op).symm (𝟙 _) }
  left_inv f := by
    ext ⟨X, ⟨⟨⟩⟩, φ⟩
    suffices yonedaEquiv.symm (φ.app (Opposite.op X) (𝟙 X)) = φ by
      dsimp
      erw [yonedaEquiv_apply]
      dsimp [CostructuredArrow.mk]
      erw [this]
    exact yonedaEquiv.injective (by aesop_cat)
  right_inv g := by
    ext X x
    dsimp
    erw [yonedaEquiv_apply]
    dsimp
    rw [yonedaEquiv_symm_app_apply]
    simp
section
example [HasColimitsOfSize.{v₁, max u₁ v₁} ℰ] :
    yoneda.HasPointwiseLeftKanExtension A := inferInstance
variable [yoneda.HasPointwiseLeftKanExtension A]
variable {A}
variable (L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ) (α : A ⟶ yoneda ⋙ L) [L.IsLeftKanExtension α]
noncomputable def restrictedYonedaHomEquiv (P : Cᵒᵖ ⥤ Type v₁) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv E).trans
    (restrictedYonedaHomEquiv' A P E)
noncomputable def yonedaAdjunction : L ⊣ restrictedYoneda A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedYonedaHomEquiv L α
      homEquiv_naturality_left_symm := fun {P Q X} f g => by
        obtain ⟨g, rfl⟩ := (restrictedYonedaHomEquiv L α Q X).surjective g
        apply (restrictedYonedaHomEquiv L α P X).injective
        simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        ext Y y
        dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        rw [assoc, assoc, ← L.map_comp_assoc]
        congr 3
        apply yonedaEquiv.injective
        simp [yonedaEquiv]
      homEquiv_naturality_right := fun {P X Y} f g => by
        apply (restrictedYonedaHomEquiv L α P Y).symm.injective
        simp only [Equiv.symm_apply_apply]
        dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro p
        rw [IsColimit.fac]
        dsimp [restrictedYoneda, yonedaEquiv]
        simp only [assoc]
        congr 3
        apply yonedaEquiv.injective
        simp [yonedaEquiv] }
include α in
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (yonedaAdjunction L α).leftAdjoint_preservesColimits
lemma isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom
variable (A)
noncomputable instance preservesColimitsOfSize_leftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} (yoneda.leftKanExtension A) :=
  (yonedaAdjunction _ (yoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits
instance : IsIso (yoneda.leftKanExtensionUnit A) :=
  isIso_of_isLeftKanExtension _ (yoneda.leftKanExtensionUnit A)
noncomputable def isExtensionAlongYoneda :
    yoneda ⋙ yoneda.leftKanExtension A ≅ A :=
  (asIso (yoneda.leftKanExtensionUnit A)).symm
end
@[reducible]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type v₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type v₁ :=
  (CategoryOfElements.π P).leftOp ⋙ yoneda
@[simps]
noncomputable def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type v₁) :
    Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app := fun x => yonedaEquiv.symm x.unop.2
      naturality := fun {x₁ x₂} f => by
        dsimp
        rw [comp_id, ← yonedaEquiv_symm_map]
        congr 1
        rw [f.unop.2] }
theorem coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type v₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simpa [coconeOfRepresentable_ι_app] using FunctorToTypes.naturality _ _ α f.op _
noncomputable def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type v₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app := fun X x => (s.ι.app (Opposite.op (Functor.elementsMk P X x))).app X (𝟙 _)
      naturality := fun X Y f => by
        ext x
        have eq₁ := congr_fun (congr_app (s.w (CategoryOfElements.homMk (P.elementsMk X x)
          (P.elementsMk Y (P.map f x)) f rfl).op) Y) (𝟙 _)
        dsimp at eq₁ ⊢
        simpa [← eq₁, id_comp] using
          congr_fun ((s.ι.app (Opposite.op (P.elementsMk X x))).naturality f) (𝟙 _) }
  fac s j := by
    ext X x
    let φ : j.unop ⟶ Functor.elementsMk P X ((yonedaEquiv.symm j.unop.2).app X x) := ⟨x.op, rfl⟩
    simpa using congr_fun (congr_app (s.ι.naturality φ.op).symm X) (𝟙 _)
  uniq s m hm := by
    ext X x
    dsimp
    rw [← hm]
    apply congr_arg
    simp [coconeOfRepresentable_ι_app, yonedaEquiv]
variable {A : C ⥤ ℰ}
example [HasColimitsOfSize.{v₁, max u₁ v₁} ℰ] :
    yoneda.HasPointwiseLeftKanExtension A :=
  inferInstance
variable [yoneda.HasPointwiseLeftKanExtension A]
section
variable (L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ) (α : A ⟶ yoneda ⋙ L)
instance [L.IsLeftKanExtension α] : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α).isIso_hom
lemma isLeftKanExtension_along_yoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ PreservesColimitsOfSize.{v₁, max u₁ v₁} L) := by
  constructor
  · intro
    exact ⟨inferInstance, preservesColimits_of_natIso
      (Functor.leftKanExtensionUnique _ (yoneda.leftKanExtensionUnit A) _ α)⟩
  · rintro ⟨_, _⟩
    apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
      (E := Functor.LeftExtension.mk _ α)
    intro P
    dsimp [Functor.LeftExtension.IsPointwiseLeftKanExtensionAt]
    apply IsColimit.ofWhiskerEquivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
    let e : CategoryOfElements.toCostructuredArrow P ⋙ CostructuredArrow.proj yoneda P ⋙ A ≅
        functorToRepresentables P ⋙ L :=
      isoWhiskerLeft _ (isoWhiskerLeft _ (asIso α)) ≪≫
        isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Iso.refl _) L
    apply (IsColimit.precomposeHomEquiv e.symm _).1
    exact IsColimit.ofIsoColimit (isColimitOfPreserves L (colimitOfRepresentable P))
      (Cocones.ext (Iso.refl _))
lemma isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ) (e : A ≅ yoneda ⋙ L)
    [PreservesColimitsOfSize.{v₁, max u₁ v₁} L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_yoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩
end
noncomputable def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ) (e : A ≅ yoneda ⋙ L)
    [PreservesColimitsOfSize.{v₁, max u₁ v₁} L] : L ≅ yoneda.leftKanExtension A :=
  have := isLeftKanExtension_of_preservesColimits L e
  Functor.leftKanExtensionUnique _ e.hom _ (yoneda.leftKanExtensionUnit A)
instance (L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ) [PreservesColimitsOfSize.{v₁, max u₁ v₁} L]
    [yoneda.HasPointwiseLeftKanExtension (yoneda ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ : yoneda ⋙ L ⟶ _) :=
  isLeftKanExtension_of_preservesColimits _ (Iso.refl _)
lemma isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type v₁) ⥤ ℰ)
    [PreservesColimitsOfSize.{v₁, max u₁ v₁} L]
    [yoneda.HasPointwiseLeftKanExtension
      (yoneda ⋙ (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint :=
  ⟨_, ⟨((opOpEquivalence C).congrLeft.symm.toAdjunction.comp
    (yonedaAdjunction _ (𝟙 _))).ofNatIsoLeft ((opOpEquivalence C).congrLeft.invFunIdAssoc L)⟩⟩
section
variable {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)
section
instance (X : C) (Y : F.op.LeftExtension (yoneda.obj X)) :
    Unique (Functor.LeftExtension.mk _ (yonedaMap F X) ⟶ Y) where
  default := StructuredArrow.homMk
      (yonedaEquiv.symm (yonedaEquiv (F := F.op.comp Y.right) Y.hom)) (by
        ext Z f
        simpa using congr_fun (Y.hom.naturality f.op).symm (𝟙 _))
  uniq φ := by
    ext1
    apply yonedaEquiv.injective
    dsimp
    simp only [Equiv.apply_symm_apply, ← StructuredArrow.w φ]
    dsimp [yonedaEquiv]
    simp only [yonedaMap_app_apply, Functor.map_id]
instance (X : C) : (yoneda.obj (F.obj X)).IsLeftKanExtension (yonedaMap F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩
end
section
variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]
noncomputable def compYonedaIsoYonedaCompLan :
    F ⋙ yoneda ≅ yoneda ⋙ F.op.lan :=
  NatIso.ofComponents (fun X => Functor.leftKanExtensionUnique _
    (yonedaMap F X) (F.op.lan.obj _) (F.op.lanUnit.app (yoneda.obj X))) (fun {X Y} f => by
      apply yonedaEquiv.injective
      have eq₁ := congr_fun ((yoneda.obj (F.obj Y)).descOfIsLeftKanExtension_fac_app
        (yonedaMap F Y) (F.op.lan.obj (yoneda.obj Y)) (F.op.lanUnit.app (yoneda.obj Y)) _) f
      have eq₂ := congr_fun (((yoneda.obj (F.obj X)).descOfIsLeftKanExtension_fac_app
        (yonedaMap F X) (F.op.lan.obj (yoneda.obj X)) (F.op.lanUnit.app (yoneda.obj X))) _) (𝟙 _)
      have eq₃ := congr_fun (congr_app (F.op.lanUnit.naturality (yoneda.map f)) _) (𝟙 _)
      dsimp at eq₁ eq₂ eq₃
      simp only [Functor.map_id] at eq₂
      simp only [id_comp] at eq₃
      simp [yonedaEquiv, eq₁, eq₂, eq₃])
@[simp]
lemma compYonedaIsoYonedaCompLan_inv_app_app_apply_eq_id (X : C) :
    ((compYonedaIsoYonedaCompLan F).inv.app X).app (Opposite.op (F.obj X))
      ((F.op.lanUnit.app (yoneda.obj X)).app _ (𝟙 X)) = 𝟙 _ :=
  (congr_fun (Functor.descOfIsLeftKanExtension_fac_app _
    (F.op.lanUnit.app (yoneda.obj X)) _ (yonedaMap F X) (Opposite.op X)) (𝟙 _)).trans (by simp)
end
namespace compYonedaIsoYonedaCompLan
variable {F}
section
variable {X : C} {G : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁} (φ : F ⋙ yoneda ⟶ yoneda ⋙ G)
def coconeApp {P : Cᵒᵖ ⥤ Type v₁} (x : P.Elements) :
    yoneda.obj x.1.unop ⟶ F.op ⋙ G.obj P := yonedaEquiv.symm
      ((G.map (yonedaEquiv.symm x.2)).app _ ((φ.app x.1.unop).app _ (𝟙 _)))
@[reassoc (attr := simp)]
lemma coconeApp_naturality {P : Cᵒᵖ ⥤ Type v₁} {x y : P.Elements} (f : x ⟶ y) :
    yoneda.map f.1.unop ≫ coconeApp φ x = coconeApp φ y := by
  have eq₁ : yoneda.map f.1.unop ≫ yonedaEquiv.symm x.2 = yonedaEquiv.symm y.2 :=
    yonedaEquiv.injective
      (by simpa only [Equiv.apply_symm_apply, ← yonedaEquiv_naturality] using f.2)
  have eq₂ := congr_fun ((G.map (yonedaEquiv.symm x.2)).naturality (F.map f.1.unop).op)
    ((φ.app x.1.unop).app _ (𝟙 _))
  have eq₃ := congr_fun (congr_app (φ.naturality f.1.unop) _) (𝟙 _)
  have eq₄ := congr_fun ((φ.app x.1.unop).naturality (F.map f.1.unop).op)
  dsimp at eq₂ eq₃ eq₄
  apply yonedaEquiv.injective
  dsimp only [coconeApp]
  rw [Equiv.apply_symm_apply, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  simp [← eq₁, ← eq₂, ← eq₃, ← eq₄, Functor.map_comp, FunctorToTypes.comp, id_comp, comp_id]
noncomputable def presheafHom (P : Cᵒᵖ ⥤ Type v₁) : P ⟶ F.op ⋙ G.obj P :=
  (colimitOfRepresentable P).desc
    (Cocone.mk _ { app := fun x => coconeApp φ x.unop })
lemma yonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type v₁) {X : C} (f : yoneda.obj X ⟶ P) :
    yonedaEquiv (f ≫ presheafHom φ P) =
      (G.map f).app (Opposite.op (F.obj X)) ((φ.app X).app _ (𝟙 _)) := by
  obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective f
  erw [(colimitOfRepresentable P).fac _ (Opposite.op (P.elementsMk _ x))]
  dsimp only [coconeApp]
  apply Equiv.apply_symm_apply
lemma yonedaEquiv_presheafHom_yoneda_obj (X : C) :
    yonedaEquiv (presheafHom φ (yoneda.obj X)) =
      ((φ.app X).app (F.op.obj (Opposite.op X)) (𝟙 _)) := by
  simpa using yonedaEquiv_ι_presheafHom φ (yoneda.obj X) (𝟙 _)
@[reassoc (attr := simp)]
lemma presheafHom_naturality {P Q : Cᵒᵖ ⥤ Type v₁} (f : P ⟶ Q) :
    presheafHom φ P ≫ whiskerLeft F.op (G.map f) = f ≫ presheafHom φ Q :=
  hom_ext_yoneda (fun X p => yonedaEquiv.injective (by
    rw [← assoc p f, yonedaEquiv_ι_presheafHom, ← assoc,
      yonedaEquiv_comp, yonedaEquiv_ι_presheafHom,
      whiskerLeft_app, Functor.map_comp, FunctorToTypes.comp]
    dsimp))
variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]
noncomputable def natTrans : F.op.lan ⟶ G where
  app P := (F.op.lan.obj P).descOfIsLeftKanExtension (F.op.lanUnit.app P) _ (presheafHom φ P)
  naturality {P Q} f := by
    apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
    have eq := F.op.lanUnit.naturality f
    dsimp at eq ⊢
    rw [Functor.descOfIsLeftKanExtension_fac_assoc, ← reassoc_of% eq,
      Functor.descOfIsLeftKanExtension_fac, presheafHom_naturality]
lemma natTrans_app_yoneda_obj (X : C) : (natTrans φ).app (yoneda.obj X) =
    (compYonedaIsoYonedaCompLan F).inv.app X ≫ φ.app X := by
  dsimp [natTrans]
  apply (F.op.lan.obj (yoneda.obj X)).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app _)
  rw [Functor.descOfIsLeftKanExtension_fac]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_presheafHom_yoneda_obj]
  exact congr_arg _ (compYonedaIsoYonedaCompLan_inv_app_app_apply_eq_id F X).symm
end
variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]
noncomputable def extensionHom (Φ : yoneda.LeftExtension (F ⋙ yoneda)) :
    Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ :=
  StructuredArrow.homMk (natTrans Φ.hom) (by
    ext X : 2
    dsimp
    rw [natTrans_app_yoneda_obj, Iso.hom_inv_id_app_assoc])
@[ext]
lemma hom_ext {Φ : yoneda.LeftExtension (F ⋙ yoneda)}
    (f g : Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ) :
    f = g := by
  ext P : 3
  apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
  apply (colimitOfRepresentable P).hom_ext
  intro x
  have eq := F.op.lanUnit.naturality (yonedaEquiv.symm x.unop.2)
  have eq₁ := congr_fun (congr_app (congr_app (StructuredArrow.w f) x.unop.1.unop)
    (F.op.obj x.unop.1)) (𝟙 _)
  have eq₂ := congr_fun (congr_app (congr_app (StructuredArrow.w g) x.unop.1.unop)
    (F.op.obj x.unop.1)) (𝟙 _)
  dsimp at eq₁ eq₂ eq ⊢
  simp only [reassoc_of% eq, ← whiskerLeft_comp]
  congr 2
  simp only [← cancel_epi ((compYonedaIsoYonedaCompLan F).hom.app x.unop.1.unop),
    NatTrans.naturality]
  apply yonedaEquiv.injective
  dsimp [yonedaEquiv_apply]
  rw [eq₁, eq₂]
end compYonedaIsoYonedaCompLan
variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]
noncomputable instance (Φ : StructuredArrow (F ⋙ yoneda)
    ((whiskeringLeft C (Cᵒᵖ ⥤ Type v₁) (Dᵒᵖ ⥤ Type v₁)).obj yoneda)) :
    Unique (Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ) where
  default := compYonedaIsoYonedaCompLan.extensionHom Φ
  uniq _ := compYonedaIsoYonedaCompLan.hom_ext _ _
instance : F.op.lan.IsLeftKanExtension (compYonedaIsoYonedaCompLan F).hom :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩
end
section
variable {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁)
@[simps]
def tautologicalCocone : Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app := fun X => X.hom }
def isColimitTautologicalCocone : IsColimit (tautologicalCocone P) where
  desc := fun s => by
    refine ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), ?_⟩
    intros X Y f
    ext t
    dsimp
    rw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    simpa using (s.ι.naturality
      (CostructuredArrow.homMk' (CostructuredArrow.mk (yonedaEquiv.symm t)) f.unop)).symm
  fac := by
    intro s t
    dsimp
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    dsimp only
    rw [Equiv.symm_apply_apply]
    rfl
  uniq := by
    intro s j h
    ext V x
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    dsimp
    rw [Equiv.symm_apply_apply, ← yonedaEquiv_comp]
    exact congr_arg _ (h (CostructuredArrow.mk t))
variable {I : Type v₁} [SmallCategory I] (F : I ⥤ C)
theorem final_toCostructuredArrow_comp_pre {c : Cocone (F ⋙ yoneda)} (hc : IsColimit c) :
    Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) := by
  apply Functor.final_of_isTerminal_colimit_comp_yoneda
  suffices IsTerminal (colimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt)) by
    apply IsTerminal.isTerminalOfObj (overEquivPresheafCostructuredArrow c.pt).inverse
    apply IsTerminal.ofIso this
    refine ?_ ≪≫ (preservesColimitIso (overEquivPresheafCostructuredArrow c.pt).inverse _).symm
    apply HasColimit.isoOfNatIso
    exact isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse
  apply IsTerminal.ofIso Over.mkIdTerminal
  let isc : IsColimit ((Over.forget _).mapCocone _) := isColimitOfPreserves _
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext fun i => by simp)
end
end Presheaf
end CategoryTheory