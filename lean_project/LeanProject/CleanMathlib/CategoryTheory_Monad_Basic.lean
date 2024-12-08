import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso
namespace CategoryTheory
open Category
universe v₁ u₁
variable (C : Type u₁) [Category.{v₁} C]
structure Monad extends C ⥤ C where
  η : 𝟭 _ ⟶ toFunctor
  μ : toFunctor ⋙ toFunctor ⟶ toFunctor
  assoc : ∀ X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _ := by aesop_cat
  left_unit : ∀ X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _ := by aesop_cat
  right_unit : ∀ X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _ := by aesop_cat
structure Comonad extends C ⥤ C where
  ε : toFunctor ⟶ 𝟭 _
  δ : toFunctor ⟶ toFunctor ⋙ toFunctor
  coassoc : ∀ X, NatTrans.app δ _ ≫ toFunctor.map (δ.app X) = δ.app _ ≫ δ.app _ := by
    aesop_cat
  left_counit : ∀ X : C, δ.app X ≫ ε.app (toFunctor.obj X) = 𝟙 _ := by aesop_cat
  right_counit : ∀ X : C, δ.app X ≫ toFunctor.map (ε.app X) = 𝟙 _ := by aesop_cat
variable {C}
variable (T : Monad C) (G : Comonad C)
instance coeMonad : Coe (Monad C) (C ⥤ C) :=
  ⟨fun T => T.toFunctor⟩
instance coeComonad : Coe (Comonad C) (C ⥤ C) :=
  ⟨fun G => G.toFunctor⟩
initialize_simps_projections CategoryTheory.Monad (toFunctor → coe)
initialize_simps_projections CategoryTheory.Comonad (toFunctor → coe)
attribute [reassoc (attr := simp)] Monad.left_unit Monad.right_unit
attribute [reassoc (attr := simp)] Comonad.coassoc Comonad.left_counit Comonad.right_counit
@[ext]
structure MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where
  app_η : ∀ X, T₁.η.app X ≫ app X = T₂.η.app X := by aesop_cat
  app_μ : ∀ X, T₁.μ.app X ≫ app X = (T₁.map (app X) ≫ app _) ≫ T₂.μ.app X := by
    aesop_cat
initialize_simps_projections MonadHom (+toNatTrans, -app)
@[ext]
structure ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where
  app_ε : ∀ X, app X ≫ N.ε.app X = M.ε.app X := by aesop_cat
  app_δ : ∀ X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ N.map (app X) := by aesop_cat
initialize_simps_projections ComonadHom (+toNatTrans, -app)
attribute [reassoc (attr := simp)] MonadHom.app_η MonadHom.app_μ
attribute [reassoc (attr := simp)] ComonadHom.app_ε ComonadHom.app_δ
instance : Quiver (Monad C) where
  Hom := MonadHom
instance : Quiver (Comonad C) where
  Hom := ComonadHom
@[ext]
lemma MonadHom.ext' {T₁ T₂ : Monad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  MonadHom.ext h
@[ext]
lemma ComonadHom.ext' {T₁ T₂ : Comonad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  ComonadHom.ext h
instance : Category (Monad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }
  id_comp _ := MonadHom.ext (by funext; simp only [NatTrans.id_app, id_comp])
  comp_id _ := MonadHom.ext (by funext; simp only [NatTrans.id_app, comp_id])
  assoc _ _ _ := MonadHom.ext (by funext; simp only [assoc])
instance : Category (Comonad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }
  id_comp _ := ComonadHom.ext (by funext; simp only [NatTrans.id_app, id_comp])
  comp_id _ := ComonadHom.ext (by funext; simp only [NatTrans.id_app, comp_id])
  assoc _ _ _ := ComonadHom.ext (by funext; simp only [assoc])
instance {T : Monad C} : Inhabited (MonadHom T T) :=
  ⟨𝟙 T⟩
@[simp]
theorem MonadHom.id_toNatTrans (T : Monad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl
@[simp]
theorem MonadHom.comp_toNatTrans {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl
instance {G : Comonad C} : Inhabited (ComonadHom G G) :=
  ⟨𝟙 G⟩
@[simp]
theorem ComonadHom.id_toNatTrans (T : Comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl
@[simp]
theorem comp_toNatTrans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl
@[simps]
def MonadIso.mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N)
    (f_η : ∀ (X : C), M.η.app X ≫ f.hom.app X = N.η.app X := by aesop_cat)
    (f_μ : ∀ (X : C), M.μ.app X ≫ f.hom.app X =
    (M.map (f.hom.app X) ≫ f.hom.app (N.obj X)) ≫ N.μ.app X := by aesop_cat) : M ≅ N where
  hom :=
    { toNatTrans := f.hom
      app_η := f_η
      app_μ := f_μ }
  inv :=
    { toNatTrans := f.inv
      app_η := fun X => by simp [← f_η]
      app_μ := fun X => by
        rw [← NatIso.cancel_natIso_hom_right f]
        simp only [NatTrans.naturality, Iso.inv_hom_id_app, assoc, comp_id, f_μ,
          NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
        simp }
@[simps]
def ComonadIso.mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N)
    (f_ε : ∀ (X : C), f.hom.app X ≫ N.ε.app X = M.ε.app X := by aesop_cat)
    (f_δ : ∀ (X : C), f.hom.app X ≫ N.δ.app X =
    M.δ.app X ≫ f.hom.app (M.obj X) ≫ N.map (f.hom.app X) := by aesop_cat) : M ≅ N where
  hom :=
    { toNatTrans := f.hom
      app_ε := f_ε
      app_δ := f_δ }
  inv :=
    { toNatTrans := f.inv
      app_ε := fun X => by simp [← f_ε]
      app_δ := fun X => by
        rw [← NatIso.cancel_natIso_hom_left f]
        simp only [reassoc_of% (f_δ X), Iso.hom_inv_id_app_assoc, NatTrans.naturality_assoc]
        rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
        apply (comp_id _).symm }
variable (C)
@[simps!]
def monadToFunctor : Monad C ⥤ C ⥤ C where
  obj T := T
  map f := f.toNatTrans
instance : (monadToFunctor C).Faithful where
theorem monadToFunctor_mapIso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) :
    (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f := by
  ext
  rfl
instance : (monadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (MonadIso.mk (asIso ((monadToFunctor C).map f)) f.app_η f.app_μ).isIso_hom
@[simps!]
def comonadToFunctor : Comonad C ⥤ C ⥤ C where
  obj G := G
  map f := f.toNatTrans
instance : (comonadToFunctor C).Faithful where
theorem comonadToFunctor_mapIso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) :
    (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f := by
  ext
  rfl
instance : (comonadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (ComonadIso.mk (asIso ((comonadToFunctor C).map f)) f.app_ε f.app_δ).isIso_hom
variable {C}
@[simps!]
def MonadIso.toNatIso {M N : Monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monadToFunctor C).mapIso h
@[simps!]
def ComonadIso.toNatIso {M N : Comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonadToFunctor C).mapIso h
variable (C)
namespace Monad
@[simps!]
def id : Monad C where
  toFunctor := 𝟭 C
  η := 𝟙 (𝟭 C)
  μ := 𝟙 (𝟭 C)
instance : Inhabited (Monad C) :=
  ⟨Monad.id C⟩
end Monad
namespace Comonad
@[simps!]
def id : Comonad C where
  toFunctor := 𝟭 _
  ε := 𝟙 (𝟭 C)
  δ := 𝟙 (𝟭 C)
instance : Inhabited (Comonad C) :=
  ⟨Comonad.id C⟩
end Comonad
open Iso Functor
variable {C}
namespace Monad
def transport {F : C ⥤ C} (T : Monad C) (i : (T : C ⥤ C) ≅ F) : Monad C where
  toFunctor := F
  η := T.η ≫ i.hom
  μ := (i.inv ◫ i.inv) ≫ T.μ ≫ i.hom
  left_unit X := by
    simp only [Functor.id_obj, NatTrans.comp_app, comp_obj, NatTrans.hcomp_app, Category.assoc,
      hom_inv_id_app_assoc]
    slice_lhs 1 2 => rw [← T.η.naturality (i.inv.app X), ]
    simp
  right_unit X := by
    simp only [id_obj, NatTrans.comp_app, Functor.map_comp, comp_obj, NatTrans.hcomp_app,
      Category.assoc, NatTrans.naturality_assoc]
    slice_lhs 2 4 =>
      simp only [← T.map_comp]
    simp
  assoc X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc, Functor.map_comp,
      NatTrans.naturality_assoc, hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    slice_lhs 4 5 => rw [← T.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp]
    slice_lhs 1 2 => rw [← T.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc, NatIso.cancel_natIso_hom_right]
    rw [← T.μ.naturality]
    simp [T.assoc X]
end Monad
namespace Comonad
def transport {F : C ⥤ C} (T : Comonad C) (i : (T : C ⥤ C) ≅ F) : Comonad C where
  toFunctor := F
  ε := i.inv ≫ T.ε
  δ := i.inv ≫ T.δ ≫ (i.hom ◫ i.hom)
  right_counit X := by
    simp only [id_obj, comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc]
    slice_lhs 4 5 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, ← i.hom.naturality]
    slice_lhs 2 3 => rw [T.right_counit]
    simp
  coassoc X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc,
      NatTrans.naturality_assoc, Functor.comp_map, hom_inv_id_app_assoc,
      NatIso.cancel_natIso_inv_left]
    slice_lhs 3 4 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, assoc]
    rw [← i.hom.naturality_assoc, ← T.coassoc_assoc]
    simp only [NatTrans.naturality_assoc]
    congr 3
    simp only [← Functor.map_comp, i.hom.naturality]
end Comonad
namespace Monad
lemma map_unit_app (T : Monad C) (X : C) [IsIso T.μ] :
    T.map (T.η.app X) = T.η.app (T.obj X) := by
  simp [← cancel_mono (T.μ.app _)]
lemma isSplitMono_iff_isIso_unit (T : Monad C) (X : C) [IsIso T.μ] :
    IsSplitMono (T.η.app X) ↔ IsIso (T.η.app X) := by
  refine ⟨fun _ ↦ ⟨retraction (T.η.app X), by simp, ?_⟩, fun _ ↦ inferInstance⟩
  erw [← map_id, ← IsSplitMono.id (T.η.app X), map_comp, T.map_unit_app X, T.η.naturality]
  rfl
end Monad
namespace Comonad
lemma map_counit_app (T : Comonad C) (X : C) [IsIso T.δ] :
    T.map (T.ε.app X) = T.ε.app (T.obj X) := by
  simp [← cancel_epi (T.δ.app _)]
lemma isSplitEpi_iff_isIso_counit (T : Comonad C) (X : C) [IsIso T.δ] :
    IsSplitEpi (T.ε.app X) ↔ IsIso (T.ε.app X) := by
  refine ⟨fun _ ↦ ⟨section_ (T.ε.app X), ?_, by simp⟩, fun _ ↦ inferInstance⟩
  erw [← map_id, ← IsSplitEpi.id (T.ε.app X), map_comp, T.map_counit_app X, T.ε.naturality]
  rfl
end Comonad
end CategoryTheory