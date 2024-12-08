import Mathlib.Topology.Gluing
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
noncomputable section
open TopologicalSpace CategoryTheory Opposite Topology
open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace
open AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
open CategoryTheory.GlueData
namespace AlgebraicGeometry
universe v u
variable (C : Type u) [Category.{v} C]
namespace PresheafedSpace
structure GlueData extends CategoryTheory.GlueData (PresheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)
attribute [instance] GlueData.f_open
namespace GlueData
variable {C}
variable (D : GlueData.{v, u} C)
local notation "𝖣" => D.toGlueData
local notation "π₁ " i ", " j ", " k => pullback.fst (D.f i j) (D.f i k)
local notation "π₂ " i ", " j ", " k => pullback.snd (D.f i j) (D.f i k)
set_option quotPrecheck false
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp
set_option quotPrecheck false
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp
abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }
theorem ι_isOpenEmbedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]
  erw [coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)
@[deprecated (since := "2024-10-18")]
alias ι_openEmbedding := ι_isOpenEmbedding
theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' ((π₁ i, j, k) ⁻¹' S) = D.f i k ⁻¹' (D.f i j '' S) := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁, ← eq₂]
  erw [coe_comp]
  rw [Set.image_comp]
  erw [coe_comp]
  rw [Set.preimage_comp, Set.image_preimage_eq, TopCat.pullback_snd_image_fst_preimage]
  · rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
@[simp, reassoc]
theorem f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) :
    (D.f_open i j).invApp _ U ≫ (D.f i k).c.app _ =
      (π₁ i, j, k).c.app (op U) ≫
        (π₂⁻¹ i, j, k) (unop _) ≫
          (D.V _).presheaf.map
            (eqToHom
              (by
                delta IsOpenImmersion.opensFunctor
                dsimp only [Functor.op, IsOpenMap.functor, Opens.map, unop_op]
                congr
                apply pullback_base)) := by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp _ U)), IsIso.inv_hom_id_assoc,
    IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  convert (Category.comp_id ((f D.toGlueData i k).c.app _)).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl
set_option backward.isDefEq.lazyWhnfCore false in 
theorem snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    ∃ eq,
      (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eqToHom eq) =
        (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) := by
  fconstructor
  · delta IsOpenImmersion.opensFunctor
    dsimp only [Functor.op, Opens.map, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr
    have := (𝖣.t_fac k i j).symm
    rw [← IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    replace this := congr_arg (ContinuousMap.toFun ·) this
    dsimp at this
    rw [coe_comp, coe_comp] at this
    rw [this, Set.image_comp, Set.image_comp, Set.preimage_image_eq]
    swap
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [← comp_apply, ← comp_base, D.t_inv, id_base, id_apply]
    refine congr_arg (_ '' ·) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · intro x
      rw [← comp_apply, ← comp_base, IsIso.inv_hom_id, id_base, id_apply]
    · intro x
      rw [← comp_apply, ← comp_base, IsIso.hom_inv_id, id_base, id_apply]
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    erw [← comp_c_app]
    rw [congr_app (D.t_fac k i j), comp_c_app]
    simp_rw [Category.assoc]
    erw [IsOpenImmersion.inv_naturality, IsOpenImmersion.inv_naturality_assoc,
      IsOpenImmersion.app_inv_app'_assoc]
    · simp_rw [← (𝖣.V (k, i)).presheaf.map_comp]; rfl
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv, id_base, TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 2
    rw [IsIso.inv_comp_eq, 𝖣.t_fac_assoc, 𝖣.t_inv, Category.comp_id]
set_option backward.isDefEq.lazyWhnfCore false in 
@[simp, reassoc]
theorem snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ =
      (D.t' k i j).c.app _ ≫
        (π₁⁻¹ k, j, i) (unop _) ≫
          (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k U).choose.symm) := by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]
variable [HasLimits C]
theorem ι_image_preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) :
    (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).isOpenMap.functor.obj U) =
      (opensFunctor (D.f j i)).obj
        ((Opens.map (𝖣.t j i).base).obj ((Opens.map (𝖣.f i j).base).obj U)) := by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.functor_obj_coe]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i, ←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  erw [coe_comp, coe_comp, coe_comp]
  rw [Set.image_comp, Set.preimage_comp]
  erw [Set.preimage_image_eq]
  · refine Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) ?_
    dsimp
    rw [Set.image_comp]
    refine congr_arg (_ '' ·) ?_
    rw [Set.eq_preimage_iff_image_eq, ← Set.image_comp]
    swap
    · exact CategoryTheory.ConcreteCategory.bijective_of_isIso (C := TopCat) _
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [← coe_comp, ← TopCat.mono_iff_injective]
    infer_instance
def opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶
    (D.U j).presheaf.obj (op <|
      (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).isOpenMap.functor.obj U)) :=
  (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp _ (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op
theorem opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) :
    ∃ eq,
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
        ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
          (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom eq) := by
  constructor
  · delta opensImagePreimageMap
    simp_rw [Category.assoc]
    rw [(D.f j k).c.naturality, f_invApp_f_app_assoc]
    · erw [← (D.V (j, k)).presheaf.map_comp]
      · simp_rw [← Category.assoc]
        erw [← comp_c_app, ← comp_c_app]
        · simp_rw [Category.assoc]
          dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
          rw [eqToHom_map (Opens.map _), eqToHom_op, eqToHom_trans]
          congr
theorem opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).choose) :=
  (opensImagePreimageMap_app' D i j k U).choose_spec
theorem opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
    (f' : _ ⟶ X') :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map
            (eqToHom (opensImagePreimageMap_app' D i j k U).choose) ≫ f' := by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)
abbrev diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) :
    (WalkingMultispan D.diagram.fstFrom D.diagram.sndFrom)ᵒᵖ ⥤ C :=
  componentwiseDiagram 𝖣.diagram.multispan ((D.ι_isOpenEmbedding i).isOpenMap.functor.obj U)
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))
def ιInvAppπApp {i : D.J} (U : Opens (D.U i).carrier) (j) :
    (𝖣.U i).presheaf.obj (op U) ⟶ (D.diagramOverOpen U).obj (op j) := by
  rcases j with (⟨j, k⟩ | j)
  · refine
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom ?_)
    rw [Functor.op_obj]
    congr 1; ext1
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.functor_obj_coe]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    suffices D.f j k ≫ D.ι j = colimit.ι D.diagram.multispan (WalkingMultispan.left (j, k)) by
      rw [this]
      rfl
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
  · exact D.opensImagePreimageMap i j U
set_option maxHeartbeats 600000 in
def ιInvApp {i : D.J} (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ limit (D.diagramOverOpen U) :=
  limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X using Opposite.rec' with | h X => ?_
            induction Y using Opposite.rec' with | h Y => ?_
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · erw [Category.id_comp, CategoryTheory.Functor.map_id]
              rw [Category.comp_id]
            · erw [Category.id_comp]; congr 1
            erw [Category.id_comp]
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            rw [opensImagePreimageMap_app_assoc]
            simp_rw [Category.assoc]
            rw [opensImagePreimageMap_app_assoc, (D.t j k).c.naturality_assoc,
                snd_invApp_t_app_assoc,
                ← PresheafedSpace.comp_c_app_assoc]
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc, 𝖣.t'_comp_eq_pullbackSymmetry_assoc,
                pullbackSymmetry_hom_comp_snd_assoc, pullback.condition, 𝖣.t_fac_assoc]
            rw [congr_app this,
                PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp,
                IsOpenImmersion.inv_invApp]
            simp_rw [Category.assoc]
            erw [NatTrans.naturality_assoc, ← PresheafedSpace.comp_c_app_assoc,
              congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc]
            erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.inv_naturality_assoc,
              IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc]
            rw [← (D.V (j, k)).presheaf.map_comp]
            erw [← (D.V (j, k)).presheaf.map_comp]
            repeat rw [← (D.V (j, k)).presheaf.map_comp]
            exact congr_arg ((D.V (j, k)).presheaf.map ·) rfl } }
theorem ιInvApp_π {i : D.J} (U : Opens (D.U i).carrier) :
    ∃ eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).presheaf.map (eqToHom eq) := by
  fconstructor
  · congr; ext1; change _ = _ ⁻¹' (_ '' _); ext1 x
    simp only [SetLike.mem_coe, diagram_l, diagram_r, unop_op, Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨y, h1, h2⟩
    convert h1 using 1
    delta ι Multicoequalizer.π at h2
    apply_fun (D.ι _).base
    · exact h2.symm
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      dsimp at this
      rw [← this, coe_comp]
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      rw [← TopCat.mono_iff_injective]
      infer_instance
  delta ιInvApp
  rw [limit.lift_π]
  change D.opensImagePreimageMap i i U = _
  dsimp [opensImagePreimageMap]
  rw [congr_app (D.t_id _), id_c_app, ← Functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  · simp only [eqToHom_op, eqToHom_trans, eqToHom_map (Functor.op _), ← Functor.map_comp]
    rfl
  · rw [Set.range_eq_univ.mpr _]
    · simp
    · rw [← TopCat.epi_iff_surjective]
      infer_instance
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv
theorem π_ιInvApp_π (i j : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U ≫ D.diagramOverOpenπ U j =
      D.diagramOverOpenπ U j := by
  rw [← @cancel_mono
          (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
            (Quiver.Hom.op (WalkingMultispan.Hom.snd (i, j))) ≫ 𝟙 _) ..]
  · simp_rw [Category.assoc]
    rw [limit.w_assoc]
    erw [limit.lift_π_assoc]
    rw [Category.comp_id, Category.comp_id]
    change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
    rw [congr_app (D.t_id _), id_c_app]
    simp_rw [Category.assoc]
    rw [← Functor.map_comp_assoc]
    erw [IsOpenImmersion.inv_naturality_assoc]
    erw [IsOpenImmersion.app_invApp_assoc]
    iterate 3 rw [← Functor.map_comp_assoc]
    rw [NatTrans.naturality_assoc]
    erw [← (D.V (i, j)).presheaf.map_comp]
    convert
      limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
  · rw [Category.comp_id]
    apply (config := { allowSynthFailures := true }) mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply (config := { allowSynthFailures := true }) mono_comp
    · erw [D.ι_image_preimage_eq i j U]
      infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance
theorem π_ιInvApp_eq_id (i : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U = 𝟙 _ := by
  ext j
  induction j using Opposite.rec' with | h j => ?_
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ιInvApp_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ιInvApp_π
instance componentwise_diagram_π_isIso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) := by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  constructor
  · apply π_ιInvApp_eq_id
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) where
  base_open := D.ι_isOpenEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst ?_
      erw [← D.toTopGlueData.preimage_range j i]
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _, ←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base, comp_base] at this
        replace this := reassoc_of% this
        exact this _
      rw [← Set.image_subset_iff, ← Set.image_univ, ← Set.image_comp, Set.image_univ]
      erw [← coe_comp]
      rw [this, coe_comp, ← Set.image_univ, Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ _; rw [← cancel_mono (D.f i j)]; erw [e₁]; rw [IsOpenImmersion.lift_fac]
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
end GlueData
end PresheafedSpace
namespace SheafedSpace
structure GlueData extends CategoryTheory.GlueData (SheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, SheafedSpace.IsOpenImmersion (f i j)
attribute [instance] GlueData.f_open
namespace GlueData
variable {C}
variable (D : GlueData C)
local notation "𝖣" => D.toGlueData
abbrev toPresheafedSpaceGlueData : PresheafedSpace.GlueData C :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }
variable [HasLimits C]
abbrev isoPresheafedSpace :
    𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToPresheafedSpace
theorem ι_isoPresheafedSpace_inv (i : D.J) :
    D.toPresheafedSpaceGlueData.toGlueData.ι i ≫ D.isoPresheafedSpace.inv = 𝖣.ι i :=
  𝖣.ι_gluedIso_inv _ _
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [← D.ι_isoPresheafedSpace_inv]
  have := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i
  infer_instance
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)
end GlueData
end SheafedSpace
namespace LocallyRingedSpace
structure GlueData extends CategoryTheory.GlueData LocallyRingedSpace where
  f_open : ∀ i j, LocallyRingedSpace.IsOpenImmersion (f i j)
attribute [instance] GlueData.f_open
namespace GlueData
variable (D : GlueData.{u})
local notation "𝖣" => D.toGlueData
abbrev toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }
abbrev isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToSheafedSpace
theorem ι_isoSheafedSpace_inv (i : D.J) :
    D.toSheafedSpaceGlueData.toGlueData.ι i ≫ D.isoSheafedSpace.inv = (𝖣.ι i).1 :=
  𝖣.ι_gluedIso_inv forgetToSheafedSpace i
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  delta IsOpenImmersion; rw [← D.ι_isoSheafedSpace_inv]
  apply (config := { allowSynthFailures := true }) PresheafedSpace.IsOpenImmersion.comp
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i
instance (i j k : D.J) : PreservesLimit (cospan (𝖣.f i j) (𝖣.f i k)) forgetToSheafedSpace :=
  inferInstance
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCatMax.{u, u}) ⋙
      forget TopCat.{u}) x
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)
end GlueData
end LocallyRingedSpace
end AlgebraicGeometry