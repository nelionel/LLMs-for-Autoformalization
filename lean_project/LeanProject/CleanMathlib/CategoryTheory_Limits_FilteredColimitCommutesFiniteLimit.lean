import Mathlib.CategoryTheory.Limits.ColimitLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.Data.Countable.Small
assert_not_exists map_ne_zero
assert_not_exists Field
universe w v₁ v₂ v u₁ u₂ u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits.Types
  CategoryTheory.Limits.Types.FilteredColimit
namespace CategoryTheory.Limits
section
variable {J : Type u₁} {K : Type u₂} [Category.{v₁} J] [Category.{v₂} K] [Small.{v} K]
@[ext] lemma comp_lim_obj_ext {j : J} {G : J ⥤ K ⥤ Type v} (x y : (G ⋙ lim).obj j)
    (w : ∀ (k : K), limit.π (G.obj j) k x = limit.π (G.obj j) k y) : x = y :=
  limit_ext _ x y w
variable (F : J × K ⥤ Type v)
open CategoryTheory.Prod
variable [IsFiltered K]
section
variable [Finite J]
theorem colimitLimitToLimitColimit_injective :
    Function.Injective (colimitLimitToLimitColimit F) := by
  classical
    cases nonempty_fintype J
    intro x y h
    obtain ⟨kx, x, rfl⟩ := jointly_surjective' x
    obtain ⟨ky, y, rfl⟩ := jointly_surjective' y
    dsimp at x y
    replace h := fun j => congr_arg (limit.π (curry.obj F ⋙ colim) j) h
    simp? [colimit_eq_iff] at h says
      simp only [Functor.comp_obj, colim_obj, ι_colimitLimitToLimitColimit_π_apply,
        colimit_eq_iff, curry_obj_obj_obj, curry_obj_obj_map] at h
    let k j := (h j).choose
    let f : ∀ j, kx ⟶ k j := fun j => (h j).choose_spec.choose
    let g : ∀ j, ky ⟶ k j := fun j => (h j).choose_spec.choose_spec.choose
    have w :
      ∀ j, F.map ((𝟙 j, f j) :
        (j, kx) ⟶ (j, k j)) (limit.π ((curry.obj (swap K J ⋙ F)).obj kx) j x) =
          F.map ((𝟙 j, g j) : (j, ky) ⟶ (j, k j))
            (limit.π ((curry.obj (swap K J ⋙ F)).obj ky) j y) :=
      fun j => (h j).choose_spec.choose_spec.choose_spec
    let O : Finset K := Finset.univ.image k ∪ {kx, ky}
    have kxO : kx ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kyO : ky ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kjO : ∀ j, k j ∈ O := fun j => Finset.mem_union.mpr (Or.inl (by simp))
    let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      (Finset.univ.image fun j : J =>
          ⟨kx, k j, kxO, Finset.mem_union.mpr (Or.inl (by simp)), f j⟩) ∪
        Finset.univ.image fun j : J => ⟨ky, k j, kyO, Finset.mem_union.mpr (Or.inl (by simp)), g j⟩
    obtain ⟨S, T, W⟩ := IsFiltered.sup_exists O H
    have fH : ∀ j, (⟨kx, k j, kxO, kjO j, f j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
      fun j =>
      Finset.mem_union.mpr
        (Or.inl
          (by
            simp only [true_and, Finset.mem_univ, eq_self_iff_true, exists_prop_of_true,
              Finset.mem_image, heq_iff_eq]
            refine ⟨j, ?_⟩
            simp only [heq_iff_eq] ))
    have gH :
      ∀ j, (⟨ky, k j, kyO, kjO j, g j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
      fun j =>
      Finset.mem_union.mpr
        (Or.inr
          (by
            simp only [true_and, Finset.mem_univ, eq_self_iff_true, exists_prop_of_true,
              Finset.mem_image, heq_iff_eq]
            refine ⟨j, ?_⟩
            simp only [heq_iff_eq]))
    apply colimit_sound' (T kxO) (T kyO)
    ext j
    simp only [Functor.comp_map, Limit.map_π_apply, curry_obj_map_app, swap_map]
    rw [← W _ _ (fH j), ← W _ _ (gH j)]
    simp [Limit.map_π_apply, w]
end
end
section
variable {J : Type u₁} {K : Type u₂} [SmallCategory J] [Category.{v₂} K] [Small.{v} K]
variable [FinCategory J]
variable (F : J × K ⥤ Type v)
open CategoryTheory.Prod
variable [IsFiltered K]
theorem colimitLimitToLimitColimit_surjective :
    Function.Surjective (colimitLimitToLimitColimit F) := by
  classical
    intro x
    have z := fun j => jointly_surjective' (limit.π (curry.obj F ⋙ Limits.colim) j x)
    let k : J → K := fun j => (z j).choose
    let y : ∀ j, F.obj (j, k j) := fun j => (z j).choose_spec.choose
    have e : ∀ j,
        colimit.ι ((curry.obj F).obj j) (k j) (y j) = limit.π (curry.obj F ⋙ Limits.colim) j x :=
      fun j => (z j).choose_spec.choose_spec
    clear_value k y
    clear z
    let k' : K := IsFiltered.sup (Finset.univ.image k) ∅
    have g : ∀ j, k j ⟶ k' := fun j => IsFiltered.toSup (Finset.univ.image k) ∅ (by simp)
    clear_value k'
    have w :
      ∀ {j j' : J} (f : j ⟶ j'),
        colimit.ι ((curry.obj F).obj j') k' (F.map ((𝟙 j', g j') : (j', k j') ⟶ (j', k')) (y j')) =
          colimit.ι ((curry.obj F).obj j') k' (F.map ((f, g j) : (j, k j) ⟶ (j', k')) (y j)) := by
      intro j j' f
      have t : (f, g j) =
          (((f, 𝟙 (k j)) : (j, k j) ⟶ (j', k j)) ≫ (𝟙 j', g j) : (j, k j) ⟶ (j', k')) := by
        simp only [id_comp, comp_id, prod_comp]
      erw [Colimit.w_apply, t, FunctorToTypes.map_comp_apply, Colimit.w_apply, e,
        ← Limit.w_apply.{u₁, v, u₁} f, ← e]
      simp only [Functor.comp_map, Types.Colimit.ι_map_apply, curry_obj_map_app]
    simp_rw [colimit_eq_iff] at w
    let kf : ∀ {j j'} (_ : j ⟶ j'), K := fun f => (w f).choose
    let gf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun f => (w f).choose_spec.choose
    let hf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun f =>
      (w f).choose_spec.choose_spec.choose
    have wf :
      ∀ {j j'} (f : j ⟶ j'),
        F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j') =
          F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j) :=
      fun {j j'} f => by
      have q :
        ((curry.obj F).obj j').map (gf f) (F.map ((𝟙 j', g j') : (j', k j') ⟶ (j', k')) (y j')) =
          ((curry.obj F).obj j').map (hf f) (F.map ((f, g j) : (j, k j) ⟶ (j', k')) (y j)) :=
        (w f).choose_spec.choose_spec.choose_spec
      rw [curry_obj_obj_map, curry_obj_obj_map] at q
      simp_rw [← FunctorToTypes.map_comp_apply, CategoryStruct.comp] at q
      convert q <;> simp only [comp_id]
    clear_value kf gf hf
    clear w
    let O :=
      (Finset.univ.biUnion fun j => Finset.univ.biUnion fun j' => Finset.univ.image
        (@kf j j')) ∪ {k'}
    have kfO : ∀ {j j'} (f : j ⟶ j'), kf f ∈ O := fun {j} {j'} f =>
      Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
            Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ j',
              Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩⟩))
    have k'O : k' ∈ O := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      Finset.univ.biUnion fun j : J =>
        Finset.univ.biUnion fun j' : J =>
          Finset.univ.biUnion fun f : j ⟶ j' =>
            {⟨k', kf f, k'O, kfO f, gf f⟩, ⟨k', kf f, k'O, kfO f, hf f⟩}
    obtain ⟨k'', i', s'⟩ := IsFiltered.sup_exists O H
    let i : ∀ {j j'} (f : j ⟶ j'), kf f ⟶ k'' := fun {j} {j'} f => i' (kfO f)
    have s : ∀ {j₁ j₂ j₃ j₄} (f : j₁ ⟶ j₂) (f' : j₃ ⟶ j₄), gf f ≫ i f = hf f' ≫ i f' := by
      intros j₁ j₂ j₃ j₄ f f'
      rw [s', s']
      · exact k'O
      · exact Finset.mem_biUnion.mpr ⟨j₃, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₄, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f', Finset.mem_univ _, by
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
                or_true]
              trivial⟩⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, by
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
                true_or]
              trivial⟩⟩⟩
    clear_value i
    clear s' i' H kfO k'O O
    fconstructor
    · 
      apply colimit.ι (curry.obj (swap K J ⋙ F) ⋙ Limits.lim) k'' _
      dsimp
      apply Limit.mk
      swap
      ·
        exact fun j => F.map (⟨𝟙 j, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)⟩ : (j, k j) ⟶ (j, k'')) (y j)
      · 
        dsimp
        intro j j' f
        simp only [← FunctorToTypes.map_comp_apply, prod_comp, id_comp, comp_id]
        calc
          F.map ((f, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)) : (j, k j) ⟶ (j', k'')) (y j) =
              F.map ((f, g j ≫ hf f ≫ i f) : (j, k j) ⟶ (j', k'')) (y j) := by
            rw [s (𝟙 j) f]
          _ =
              F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k''))
                (F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j)) := by
            rw [← FunctorToTypes.map_comp_apply, prod_comp, comp_id, assoc]
          _ =
              F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k''))
                (F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j')) := by
            rw [← wf f]
          _ = F.map ((𝟙 j', g j' ≫ gf f ≫ i f) : (j', k j') ⟶ (j', k'')) (y j') := by
            rw [← FunctorToTypes.map_comp_apply, prod_comp, id_comp, assoc]
          _ = F.map ((𝟙 j', g j' ≫ gf (𝟙 j') ≫ i (𝟙 j')) : (j', k j') ⟶ (j', k'')) (y j') := by
            rw [s f (𝟙 j'), ← s (𝟙 j') (𝟙 j')]
    · 
      apply limit_ext
      intro j
      simp only [id, ← e, Limits.ι_colimitLimitToLimitColimit_π_apply,
          colimit_eq_iff, Bifunctor.map_id_comp, types_comp_apply, curry_obj_obj_map,
          Functor.comp_obj, colim_obj, Limit.π_mk]
      refine ⟨k'', 𝟙 k'', g j ≫ gf (𝟙 j) ≫ i (𝟙 j), ?_⟩
      rw [Bifunctor.map_id_comp, Bifunctor.map_id_comp, types_comp_apply, types_comp_apply,
        Bifunctor.map_id, types_id_apply]
instance colimitLimitToLimitColimit_isIso : IsIso (colimitLimitToLimitColimit F) :=
  (isIso_iff_bijective _).mpr
    ⟨colimitLimitToLimitColimit_injective F, colimitLimitToLimitColimit_surjective F⟩
instance colimitLimitToLimitColimitCone_iso (F : J ⥤ K ⥤ Type v) :
    IsIso (colimitLimitToLimitColimitCone F) := by
  have : IsIso (colimitLimitToLimitColimitCone F).hom := by
    suffices IsIso (colimitLimitToLimitColimit (uncurry.obj F) ≫
        lim.map (whiskerRight (currying.unitIso.app F).inv colim)) by
      apply IsIso.comp_isIso
    infer_instance
  apply Cones.cone_iso_of_hom_iso
noncomputable instance filtered_colim_preservesFiniteLimits_of_types :
    PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{v₂}
  intro J _ _
  refine ⟨fun {F} => ⟨fun {c} hc => ⟨IsLimit.ofIsoLimit (limit.isLimit _) ?_⟩⟩⟩
  symm
  trans colim.mapCone (limit.cone F)
  · exact Functor.mapIso _ (hc.uniqueUpToIso (limit.isLimit F))
  · exact asIso (colimitLimitToLimitColimitCone F)
variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]
section
variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]
variable [PreservesLimitsOfShape J (forget C)]
noncomputable instance filtered_colim_preservesFiniteLimits :
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) :=
  haveI : PreservesLimitsOfShape J ((colim : (K ⥤ C) ⥤ _) ⋙ forget C) :=
    preservesLimitsOfShape_of_natIso (preservesColimitNatIso _).symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (forget C)
end
attribute [local instance] reflectsLimitsOfShape_of_reflectsIsomorphisms
noncomputable instance [PreservesFiniteLimits (forget C)] [PreservesColimitsOfShape K (forget C)]
    [HasFiniteLimits C] [HasColimitsOfShape K C] [(forget C).ReflectsIsomorphisms] :
    PreservesFiniteLimits (colim : (K ⥤ C) ⥤ _) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{v}
  intro J _ _
  infer_instance
end
section
variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]
noncomputable def colimitLimitIso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm
@[reassoc (attr := simp)]
theorem ι_colimitLimitIso_limit_π (F : J ⥤ K ⥤ C) (a) (b) :
    colimit.ι (limit F) a ≫ (colimitLimitIso F).hom ≫ limit.π (colimit F.flip) b =
      (limit.π F b).app a ≫ (colimit.ι F.flip a).app b := by
  dsimp [colimitLimitIso]
  simp only [Functor.mapCone_π_app, Iso.symm_hom,
    Limits.limit.conePointUniqueUpToIso_hom_comp_assoc, Limits.limit.cone_π,
    Limits.colimit.ι_map_assoc, Limits.colimitFlipIsoCompColim_inv_app, assoc,
    Limits.HasLimit.isoOfNatIso_hom_π]
  congr 1
  simp only [← Category.assoc, Iso.comp_inv_eq,
    Limits.colimitObjIsoColimitCompEvaluation_ι_app_hom,
    Limits.HasColimit.isoOfNatIso_ι_hom, NatIso.ofComponents_hom_app]
  dsimp
  simp
end
end CategoryTheory.Limits