import Mathlib.CategoryTheory.GlueData
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Tactic.Generalize
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
noncomputable section
open CategoryTheory TopologicalSpace Topology
universe v u
open CategoryTheory.Limits
namespace TopCat
structure GlueData extends CategoryTheory.GlueData TopCat where
  f_open : ∀ i j, IsOpenEmbedding (f i j)
  f_mono i j := (TopCat.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective
namespace GlueData
variable (D : GlueData.{u})
local notation "𝖣" => D.toGlueData
theorem π_surjective : Function.Surjective 𝖣.π :=
  (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance
theorem isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ ∀ i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff]
  dsimp only [GlueData.diagram_l, GlueData.diagram_left, GlueData.diagram_r, GlueData.diagram_right,
    parallelPair_obj_one]
  rw [colimit_isOpen_iff.{_,u}]  
  constructor
  · intro h j; exact h ⟨j⟩
  · intro h j; cases j; apply h
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : _) (y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget TopCat) x
def Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop :=
  a = b ∨ ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2
theorem rel_equiv : Equivalence D.Rel :=
  ⟨fun x => Or.inl (refl x), by
    rintro a b (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    exacts [Or.inl rfl, Or.inr ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩], by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    · exact id
    rintro (⟨⟨⟩⟩ | ⟨y, e₃, e₄⟩)
    · exact Or.inr ⟨x, e₁, e₂⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _  ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      erw [pullbackIsoProdSubtype_inv_fst_apply, D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    right
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp only at *
    substs eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨ContinuousMap.congr_fun h₁ z, ContinuousMap.congr_fun h₂ z⟩⟩
open CategoryTheory.Limits.WalkingParallelPair
theorem eqvGen_of_π_eq
    {x y : sigmaObj (β := D.toGlueData.J) (C := TopCat) D.toGlueData.U}
    (h : 𝖣.π x = 𝖣.π y) :
    Relation.EqvGen
      (Types.CoequalizerRel
        (X := sigmaObj (β := D.toGlueData.diagram.L) (C := TopCat) (D.toGlueData.diagram).left)
        (Y := sigmaObj (β := D.toGlueData.diagram.R) (C := TopCat) (D.toGlueData.diagram).right)
        𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap)
      x y := by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h := (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π, ContinuousMap.toFun_eq_coe] at h
    rw [← ι_preservesColimitIso_hom, forget_map_eq_coe, types_comp_apply, h]
    simp
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  rw [colimit.ι_map_assoc, diagramIsoParallelPair_hom_app, eqToHom_refl,
    colimit.isoColimitCocone_ι_hom, types_comp_apply, types_id_apply, types_comp_apply,
    types_id_apply] at this
  exact Quot.eq.1 this
theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine Relation.EqvGen.mono ?_ (D.eqvGen_of_π_eq h : _)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    simp only [forget_map_eq_coe]
    erw [TopCat.comp_app, sigmaIsoSigma_inv_apply, ← comp_apply, ← comp_apply,
      colimit.ι_desc_assoc, ← comp_apply, ← comp_apply, colimit.ι_desc_assoc]
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact Or.inr ⟨y, ⟨rfl, rfl⟩⟩
  · rintro (⟨⟨⟩⟩ | ⟨z, e₁, e₂⟩)
    · rfl
    dsimp only at *
    rw [← e₁, ← e₂] at *
    rw [D.glue_condition_apply]
theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩ | ⟨_, e₁, e₂⟩)
  · rfl
  · dsimp only at *
    rw [← e₁, ← e₂]
    simp
instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)
theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) ∩ Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨⟨⟩⟩ | ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · exact ⟨inv (D.f i i) x₁, by
        rw [TopCat.comp_app, CategoryTheory.IsIso.inv_hom_id_apply, eq₁]⟩
    · 
      dsimp only at *
      substs eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx
theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j), ← Set.image_univ, ←
    Set.image_univ, ← Set.image_comp, ← coe_comp, Set.image_univ, Set.image_univ, ← image_inter,
    Set.preimage_range_inter]
theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) := by
  have : D.f _ _ ⁻¹' (𝖣.ι j ⁻¹' (𝖣.ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    generalize 𝖣.ι i '' U = U' 
    simp only [GlueData.diagram_l, GlueData.diagram_r, Set.mem_preimage, coe_comp,
      Function.comp_apply]
    rw [D.glue_condition_apply]
  rw [← this, Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)
theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = (D.t i j ≫ D.f _ _) '' (D.f _ _ ⁻¹' U) := by
  convert D.preimage_image_eq_image i j U using 1
  rw [coe_comp, coe_comp]
  show (fun x => ((forget TopCat).map _ ((forget TopCat).map _ x))) '' _ = _
  rw [← Set.image_image]
  refine congr_arg ?_ ?_
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [← isIso_iff_bijective]
  apply (forget TopCat).map_isIso
theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' (U : Set (D.U i))) := by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).continuous_toFun.isOpen_preimage
  exact U.isOpen
theorem ι_isOpenEmbedding (i : D.J) : IsOpenEmbedding (𝖣.ι i) :=
  .of_continuous_injective_isOpenMap (𝖣.ι i).continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩
@[deprecated (since := "2024-10-18")]
alias ι_openEmbedding := ι_isOpenEmbedding
structure MkCore where
  {J : Type u}
  U : J → TopCat.{u}
  V : ∀ i, J → Opens (U i)
  t : ∀ i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → (((↑) : (V j i) → (U j)) (t i j x)) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      (((↑) : (V k j) → (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) → (U k)) (t i k ⟨x, h⟩)
theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert Subtype.eq this
  rw [h.V_id]
  trivial
instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion' (h.V i k).inclusion' ⟶
      pullback (h.V j k).inclusion' (h.V j i).inclusion' := by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop
def mk' (h : MkCore.{u}) : TopCat.GlueData where
  J := h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := by
    beta_reduce
    exact (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc, Category.assoc, pullbackIsoProdSubtype_inv_snd, ← Iso.eq_inv_comp,
      pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp, Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rw [comp_app, ContinuousMap.coe_mk, comp_app, id_app, ContinuousMap.coe_mk, Subtype.mk_eq_mk,
      Prod.mk.inj_iff, Subtype.mk_eq_mk, Subtype.ext_iff, and_self_iff]
    convert congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h
variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)
@[simps! toGlueData_J toGlueData_U toGlueData_V toGlueData_t toGlueData_f]
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by
        refine Continuous.subtype_mk ?_ ?_
        refine Continuous.subtype_mk ?_ ?_
        continuity⟩
      V_id := fun i => by
        ext
        simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)
@[simp, elementwise nosimp]
theorem ι_fromOpenSubsetsGlue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion' _ :=
  Multicoequalizer.π_desc _ _ _ _ _
theorem fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  rw [ι_fromOpenSubsetsGlue_apply, ι_fromOpenSubsetsGlue_apply] at e
  change x = y at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  right
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩
theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s ∩ Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert hs i using 1
    erw [← ι_fromOpenSubsetsGlue, coe_comp, Set.preimage_comp]
    apply congr_arg
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self _
theorem fromOpenSubsetsGlue_isOpenEmbedding : IsOpenEmbedding (fromOpenSubsetsGlue U) :=
  .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)
@[deprecated (since := "2024-10-18")]
alias fromOpenSubsetsGlue_openEmbedding := fromOpenSubsetsGlue_isOpenEmbedding
theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Homeomorph.homeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).2 (fromOpenSubsetsGlue_isOpenMap U)
end GlueData
end TopCat