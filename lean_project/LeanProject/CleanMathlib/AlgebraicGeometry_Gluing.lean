import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open
noncomputable section
universe u
open TopologicalSpace CategoryTheory Opposite Topology
open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace
open CategoryTheory.GlueData
namespace AlgebraicGeometry
namespace Scheme
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersion (f i j)
attribute [instance] GlueData.f_open
namespace GlueData
variable (D : GlueData.{u})
local notation "𝖣" => D.toGlueData
abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }
instance (i j : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.f i j) := by
  apply GlueData.f_open
instance (i j : 𝖣.J) :
    SheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toGlueData.f i j) := by
  apply GlueData.f_open
instance (i j : 𝖣.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.f
        i j) := by
  apply GlueData.f_open
instance (i : 𝖣.J) :
    LocallyRingedSpace.IsOpenImmersion ((D.toLocallyRingedSpaceGlueData).toGlueData.ι i) := by
  apply LocallyRingedSpace.GlueData.ι_isOpenImmersion
def gluedScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  refine ⟨_, ((D.U i).affineCover.map y).toLRSHom ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ?_⟩
  constructor
  · erw [TopCat.coe_comp, Set.range_comp] 
    refine Set.mem_image_of_mem _ ?_
    exact (D.U i).affineCover.covers y
  · infer_instance
instance : CreatesColimit 𝖣.diagram.multispan forgetToLocallyRingedSpace :=
  createsColimitOfFullyFaithfulOfIso D.gluedScheme
    (HasColimit.isoOfNatIso (𝖣.diagramIso forgetToLocallyRingedSpace).symm)
instance : PreservesColimit (𝖣.diagram.multispan) forgetToTop :=
  inferInstanceAs (PreservesColimit (𝖣.diagram).multispan (forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))
instance : HasMulticoequalizer 𝖣.diagram :=
  hasColimit_of_created _ forgetToLocallyRingedSpace
abbrev glued : Scheme :=
  𝖣.glued
abbrev ι (i : D.J) : D.U i ⟶ D.glued :=
  𝖣.ι i
abbrev isoLocallyRingedSpace :
    D.glued.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToLocallyRingedSpace
theorem ι_isoLocallyRingedSpace_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i ≫
      D.isoLocallyRingedSpace.inv = (𝖣.ι i).toLRSHom :=
  𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  rw [IsOpenImmersion, ← D.ι_isoLocallyRingedSpace_inv]; infer_instance
theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    ∃ (i : D.J) (y : (D.U i).carrier), (D.ι i).base y = x :=
  𝖣.ι_jointly_surjective (forgetToTop ⋙ forget TopCat) x
@[simp (high), reassoc]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  𝖣.glue_condition i j
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)
def vPullbackConeIsLimit (i j : D.J) : IsLimit (D.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToLocallyRingedSpace i j
    (D.toLocallyRingedSpaceGlueData.vPullbackConeIsLimit _ _)
local notation "D_" => TopCat.GlueData.toGlueData <|
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
def isoCarrier :
    D.glued.carrier ≅ (D_).glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  refine LocallyRingedSpace.forgetToSheafedSpace.mapIso ?_ ≪≫
    LocallyRingedSpace.GlueData.isoSheafedSpace _
  exact Scheme.GlueData.isoLocallyRingedSpace _
@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    (D_).ι i ≫ D.isoCarrier.inv = (D.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv, GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv, Iso.trans_inv,
    Functor.mapIso_inv, Iso.trans_inv, SheafedSpace.forgetToPresheafedSpace_map, forget_map,
    forget_map, ← PresheafedSpace.comp_base, ← Category.assoc,
    D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  erw [← Category.assoc, D.toLocallyRingedSpaceGlueData.ι_isoSheafedSpace_inv i]
  change (_ ≫ D.isoLocallyRingedSpace.inv).base = _
  rw [D.ι_isoLocallyRingedSpace_inv i]
def Rel (a b : Σ i, ((D.U i).carrier : Type _)) : Prop :=
  a = b ∨
    ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).base x = b.2
theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    (𝖣.ι i).base x = (𝖣.ι j).base y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_
    (TopCat.GlueData.ι_eq_iff_rel
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData
      i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp _).eq_iff, ← comp_apply]
  · simp_rw [← D.ι_isoCarrier_inv]
    rfl 
  · infer_instance
theorem isOpen_iff (U : Set D.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((D.ι i).base ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage, TopCat.GlueData.isOpen_iff]
  apply forall_congr'
  intro i
  rw [← Set.preimage_comp, ← ι_isoCarrier_inv]
  rfl
@[simps (config := .lemmasOnly)]
def openCover (D : Scheme.GlueData) : OpenCover D.glued where
  J := D.J
  obj := D.U
  map := D.ι
  f x := (D.ι_jointly_surjective x).choose
  covers x := ⟨_, (D.ι_jointly_surjective x).choose_spec.choose_spec⟩
end GlueData
namespace Cover
variable {X : Scheme.{u}} (𝒰 : OpenCover.{u} X)
def gluedCoverT' (x y z : 𝒰.J) :
    pullback (pullback.fst (𝒰.map x) (𝒰.map y)) (pullback.fst (𝒰.map x) (𝒰.map z)) ⟶
      pullback (pullback.fst (𝒰.map y) (𝒰.map z)) (pullback.fst (𝒰.map y) (𝒰.map x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp
@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp
@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp
@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp
@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp
theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp
theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]
theorem glued_cover_cocycle (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd
@[simps]
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open _ := inferInstance
def fromGlued : 𝒰.gluedCover.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.map x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using pullback.condition
@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.J) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.map x :=
  Multicoequalizer.π_desc _ _ _ _ _
theorem fromGlued_injective : Function.Injective 𝒰.fromGlued.base := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← comp_apply, ← comp_apply] at h
  simp_rw [← Scheme.comp_base] at h
  rw [ι_fromGlued, ι_fromGlued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit Scheme.forgetToTop (𝒰.map i) (𝒰.map j))
  rw [𝒰.gluedCover.ι_eq_iff]
  right
  use e.hom ⟨⟨x, y⟩, h⟩
  constructor
  · erw [← comp_apply e.hom, IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]; rfl
  · erw [← comp_apply e.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl
instance fromGlued_stalk_iso (x : 𝒰.gluedCover.glued.carrier) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  have := stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) x
  rw [stalkMap_comp, ← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
theorem fromGlued_open_map : IsOpenMap 𝒰.fromGlued.base := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rw [𝒰.gluedCover.isOpen_iff] at hU
  use 𝒰.fromGlued.base '' U ∩ Set.range (𝒰.map (𝒰.f x)).base
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (show IsOpenImmersion (𝒰.map (𝒰.f x)) from inferInstance).base_open.isOpenMap
    convert hU (𝒰.f x) using 1
    rw [← ι_fromGlued]; erw [coe_comp]; rw [Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ 𝒰.fromGlued_injective
  · exact ⟨hx, 𝒰.covers x⟩
theorem fromGlued_isOpenEmbedding : IsOpenEmbedding 𝒰.fromGlued.base :=
  .of_continuous_injective_isOpenMap (by fun_prop) 𝒰.fromGlued_injective 𝒰.fromGlued_open_map
@[deprecated (since := "2024-10-18")]
alias fromGlued_openEmbedding := fromGlued_isOpenEmbedding
instance : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use (𝒰.gluedCover.ι (𝒰.f x)).base y
  rw [← comp_apply]
  rw [← 𝒰.ι_fromGlued (𝒰.f x)] at h
  exact h
instance fromGlued_open_immersion : IsOpenImmersion 𝒰.fromGlued :=
  IsOpenImmersion.of_stalk_iso _ 𝒰.fromGlued_isOpenEmbedding
instance : IsIso 𝒰.fromGlued :=
  let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F
def glueMorphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x = pullback.snd _ _ ≫ f y) :
    X ⟶ Y := by
  refine inv 𝒰.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact f
  rintro ⟨i, j⟩
  change pullback.fst _ _ ≫ f i = (_ ≫ _) ≫ f j
  erw [pullbackSymmetry_hom_comp_fst]
  exact hf i j
@[simp, reassoc]
theorem ι_glueMorphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x = pullback.snd _ _ ≫ f y)
    (x : 𝒰.J) : 𝒰.map x ≫ 𝒰.glueMorphisms f hf = f x := by
  rw [← ι_fromGlued, Category.assoc]
  erw [IsIso.hom_inv_id_assoc, Multicoequalizer.π_desc]
theorem hom_ext {Y : Scheme} (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi 𝒰.fromGlued]
  apply Multicoequalizer.hom_ext
  intro x
  erw [Multicoequalizer.π_desc_assoc]
  erw [Multicoequalizer.π_desc_assoc]
  exact h x
end Cover
end Scheme
end AlgebraicGeometry