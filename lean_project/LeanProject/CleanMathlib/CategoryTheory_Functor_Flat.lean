import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Bicones
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
universe w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory
open CategoryTheory.Limits
open Opposite
namespace CategoryTheory
section RepresentablyFlat
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)
class RepresentablyCoflat (F : C ⥤ D) : Prop where
  filtered : ∀ X : D, IsFiltered (CostructuredArrow F X)
attribute [instance] RepresentablyFlat.cofiltered RepresentablyCoflat.filtered
variable (F : C ⥤ D)
instance RepresentablyFlat.of_isRightAdjoint [F.IsRightAdjoint] : RepresentablyFlat F where
  cofiltered _ := IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)
instance RepresentablyCoflat.of_isLeftAdjoint [F.IsLeftAdjoint] : RepresentablyCoflat F where
  filtered _ := IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)
theorem RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := inferInstance
theorem RepresentablyCoflat.id : RepresentablyCoflat (𝟭 C) := inferInstance
instance RepresentablyFlat.comp (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
        StructuredArrow.homMk (H.map f).right (congrArg CommaMorphism.right (c₁.w f)) }
  obtain ⟨c₂⟩ := IsCofiltered.cone_nonempty H₂
  exact ⟨⟨StructuredArrow.mk (c₁.pt.hom ≫ G.map c₂.pt.hom),
    ⟨fun j => StructuredArrow.homMk (c₂.π.app j).right (by simp [← G.map_comp, (c₂.π.app j).w]),
     fun j j' f => by simpa using (c₂.w f).symm⟩⟩⟩
section
variable {F}
theorem RepresentablyFlat.of_iso [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyFlat G where
  cofiltered _ := IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)
theorem RepresentablyCoflat.of_iso [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyCoflat G where
  filtered _ := IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)
end
theorem representablyCoflat_op_iff : RepresentablyCoflat F.op ↔ RepresentablyFlat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_of_isCofiltered_op _
    suffices IsCofiltered (StructuredArrow X F)ᵒᵖᵒᵖ from
      IsCofiltered.of_equivalence (structuredArrowOpEquivalence _ _).op
    apply IsCofiltered.of_equivalence (opOpEquivalence _)
theorem representablyFlat_op_iff : RepresentablyFlat F.op ↔ RepresentablyCoflat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofiltered_of_isFiltered_op _
    suffices IsFiltered (CostructuredArrow F X)ᵒᵖᵒᵖ from
      IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).op
    apply IsFiltered.of_equivalence (opOpEquivalence _)
instance [RepresentablyFlat F] : RepresentablyCoflat F.op :=
  (representablyCoflat_op_iff F).2 inferInstance
instance [RepresentablyCoflat F] : RepresentablyFlat F.op :=
  (representablyFlat_op_iff F).2 inferInstance
instance RepresentablyCoflat.comp (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G] :
    RepresentablyCoflat (F ⋙ G) :=
  (representablyFlat_op_iff _).1 <| inferInstanceAs <| RepresentablyFlat (F.op ⋙ G.op)
end RepresentablyFlat
section HasLimit
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      intro J sJ fJ
      constructor
      infer_instance
    IsCofiltered.of_hasFiniteLimits _⟩
theorem coflat_of_preservesFiniteColimits [HasFiniteColimits C] (F : C ⥤ D)
    [PreservesFiniteColimits F] : RepresentablyCoflat F :=
  let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)
namespace PreservesFiniteLimitsOfFlat
open StructuredArrow
variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}
variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
      hc.lift <|
        (Cones.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')
theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₂]) }
  let c₁ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₁ (pre s.pt K F) : _)).obj (c.toStructuredArrowCone F f₁)
  let c₂ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₂ (pre s.pt K F) : _)).obj (c.toStructuredArrowCone F f₂)
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    convert e₁.symm.trans e₂ <;> simp [c₁, c₂]
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  have : g₁.right = g₂.right := calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      intro j; rfl
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      intro _; rfl
  calc
    f₁ = 𝟙 _ ≫ f₁ := by simp
    _ = c₀.pt.hom ≫ F.map g₁.right := g₁.w
    _ = c₀.pt.hom ≫ F.map g₂.right := by rw [this]
    _ = 𝟙 _ ≫ f₂ := g₂.w.symm
    _ = f₂ := by simp
end PreservesFiniteLimitsOfFlat
lemma preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply PreservesFiniteLimitsOfFlat.uniq F hc
        · exact h
        · exact PreservesFiniteLimitsOfFlat.fac F hc s }
lemma preservesFiniteColimits_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] :
    PreservesFiniteColimits F :=
  letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _
lemma preservesFiniteLimits_iff_flat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ↔ PreservesFiniteLimits F :=
  ⟨fun _ ↦ preservesFiniteLimits_of_flat F, fun _ ↦ flat_of_preservesFiniteLimits F⟩
lemma preservesFiniteColimits_iff_coflat [HasFiniteColimits C] (F : C ⥤ D) :
    RepresentablyCoflat F ↔ PreservesFiniteColimits F :=
  ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩
end HasLimit
section SmallCategory
variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, whiskerLeft_app]
      rfl)
variable [ConcreteCategory.{u₁} E] [HasLimits E] [HasColimits E]
variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]
variable [PreservesLimits (forget E)]
noncomputable instance lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm
instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _
variable [HasFiniteLimits C]
instance lan_preservesFiniteLimits_of_preservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  haveI := flat_of_preservesFiniteLimits F
  infer_instance
theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ => inferInstance, fun H => by
    haveI := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    haveI : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_preservesFiniteLimits⟩
lemma preservesFiniteLimits_iff_lan_preservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ↔ PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ ↦ inferInstance,
    fun _ ↦ preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ ↦ preservesLimit_of_lan_preservesLimit _ _)⟩
end SmallCategory
end CategoryTheory