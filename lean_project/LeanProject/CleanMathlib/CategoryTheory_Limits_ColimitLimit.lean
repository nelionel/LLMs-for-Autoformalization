import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
universe v₁ v₂ v u₁ u₂ u
open CategoryTheory
namespace CategoryTheory.Limits
variable {J : Type u₁} {K : Type u₂} [Category.{v₁} J] [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]
variable (F : J × K ⥤ C)
open CategoryTheory.prod
theorem map_id_left_eq_curry_map {j : J} {k k' : K} {f : k ⟶ k'} :
    F.map ((𝟙 j, f) : (j, k) ⟶ (j, k')) = ((curry.obj F).obj j).map f :=
  rfl
theorem map_id_right_eq_curry_swap_map {j j' : J} {f : j ⟶ j'} {k : K} :
    F.map ((f, 𝟙 k) : (j, k) ⟶ (j', k)) = ((curry.obj (Prod.swap K J ⋙ F)).obj k).map f :=
  rfl
variable [HasLimitsOfShape J C]
variable [HasColimitsOfShape K C]
noncomputable def colimitLimitToLimitColimit :
    colimit (curry.obj (Prod.swap K J ⋙ F) ⋙ lim) ⟶ limit (curry.obj F ⋙ colim) :=
  limit.lift (curry.obj F ⋙ colim)
    { pt := _
      π :=
        { app := fun j =>
            colimit.desc (curry.obj (Prod.swap K J ⋙ F) ⋙ lim)
              { pt := _
                ι :=
                  { app := fun k =>
                      limit.π ((curry.obj (Prod.swap K J ⋙ F)).obj k) j ≫
                        colimit.ι ((curry.obj F).obj j) k
                    naturality := by
                      intro k k' f
                      simp only [Functor.comp_obj, lim_obj, colimit.cocone_x,
                        Functor.const_obj_obj, Functor.comp_map, lim_map,
                        curry_obj_obj_obj, Prod.swap_obj, limMap_π_assoc, curry_obj_map_app,
                        Prod.swap_map, Functor.const_obj_map, Category.comp_id]
                      rw [map_id_left_eq_curry_map, colimit.w] } }
          naturality := by
            intro j j' f
            dsimp
            ext k
            simp only [Functor.comp_obj, lim_obj, Category.id_comp, colimit.ι_desc,
              colimit.ι_desc_assoc, Category.assoc, ι_colimMap,
              curry_obj_obj_obj, curry_obj_map_app]
            rw [map_id_right_eq_curry_swap_map, limit.w_assoc] } }
@[reassoc (attr := simp)]
theorem ι_colimitLimitToLimitColimit_π (j) (k) :
    colimit.ι _ k ≫ colimitLimitToLimitColimit F ≫ limit.π _ j =
      limit.π ((curry.obj (Prod.swap K J ⋙ F)).obj k) j ≫ colimit.ι ((curry.obj F).obj j) k := by
  dsimp [colimitLimitToLimitColimit]
  simp
@[simp]
theorem ι_colimitLimitToLimitColimit_π_apply [Small.{v} J] [Small.{v} K] (F : J × K ⥤ Type v)
    (j : J) (k : K) (f) : limit.π (curry.obj F ⋙ colim) j
        (colimitLimitToLimitColimit F (colimit.ι (curry.obj (Prod.swap K J ⋙ F) ⋙ lim) k f)) =
      colimit.ι ((curry.obj F).obj j) k (limit.π ((curry.obj (Prod.swap K J ⋙ F)).obj k) j f) := by
  dsimp [colimitLimitToLimitColimit]
  rw [Types.Limit.lift_π_apply]
  dsimp only
  rw [Types.Colimit.ι_desc_apply]
  dsimp
@[simps]
noncomputable def colimitLimitToLimitColimitCone (G : J ⥤ K ⥤ C) [HasLimit G] :
    colim.mapCone (limit.cone G) ⟶ limit.cone (G ⋙ colim) where
  hom :=
    colim.map (limitIsoSwapCompLim G).hom ≫
      colimitLimitToLimitColimit (uncurry.obj G : _) ≫
        lim.map (whiskerRight (currying.unitIso.app G).inv colim)
  w j := by
    dsimp
    ext1 k
    simp only [Category.assoc, limMap_π, Functor.comp_obj, colim_obj, whiskerRight_app,
      colim_map, ι_colimMap_assoc, lim_obj, limitIsoSwapCompLim_hom_app,
      ι_colimitLimitToLimitColimit_π_assoc, curry_obj_obj_obj, Prod.swap_obj,
      uncurry_obj_obj, ι_colimMap, currying_unitIso_inv_app_app_app, Category.id_comp,
      limMap_π_assoc, Functor.flip_obj_obj, flipIsoCurrySwapUncurry_hom_app_app]
    erw [limitObjIsoLimitCompEvaluation_hom_π_assoc]
end CategoryTheory.Limits