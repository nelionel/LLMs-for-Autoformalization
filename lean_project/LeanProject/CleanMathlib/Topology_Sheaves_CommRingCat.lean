import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Sheaves.Stalks
universe u v w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
namespace TopCat.Presheaf
example (X : TopCat.{u₁}) (F : Presheaf CommRingCat.{u₁} X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h
section SubmonoidPresheaf
open scoped nonZeroDivisors
variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [ConcreteCategory C]
attribute [local instance 1000] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike
structure SubmonoidPresheaf [∀ X : C, MulOneClass X] [∀ X Y : C, MonoidHomClass (X ⟶ Y) X Y]
    (F : X.Presheaf C) where
  obj : ∀ U, Submonoid (F.obj U)
  map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U ≤ (obj V).comap (F.map i)
variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)
protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
  obj U := CommRingCat.of <| Localization (G.obj U)
  map {_ _} i := CommRingCat.ofHom <| IsLocalization.map _ (F.map i) (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id (M := G.obj U) (S := Localization (G.obj U)) x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.map_comp, CommRingCat.comp_eq_ring_hom_comp]
    rw [IsLocalization.map_comp_map]
instance (U) : Algebra ((forget CommRingCat).obj (F.obj U)) (G.localizationPresheaf.obj U) :=
  show Algebra _ (Localization (G.obj U)) from inferInstance
instance (U) : IsLocalization (G.obj U) (G.localizationPresheaf.obj U) :=
  show IsLocalization (G.obj U) (Localization (G.obj U)) from inferInstance
@[simps app]
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (F.obj U) (Localization <| G.obj U)
  naturality {_ _} i := (IsLocalization.map_comp (G.map i)).symm
instance epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)
variable (F)
@[simps]
noncomputable def submonoidPresheafOfStalk (S : ∀ x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2) (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s ∈ _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩
noncomputable instance : Inhabited F.SubmonoidPresheaf :=
  ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩
noncomputable def totalQuotientPresheaf : X.Presheaf CommRingCat.{w} :=
  (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf
noncomputable def toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf :=
  SubmonoidPresheaf.toLocalizationPresheaf _
instance : Epi (toTotalQuotientPresheaf F) := epi_toLocalizationPresheaf _
instance (F : X.Sheaf CommRingCat.{w}) : Mono F.presheaf.toTotalQuotientPresheaf := by
  suffices ∀ (U : (Opens ↑X)ᵒᵖ), Mono (F.presheaf.toTotalQuotientPresheaf.app U) from
    NatTrans.mono_of_mono_app _
  intro U
  apply ConcreteCategory.mono_of_injective
  dsimp [toTotalQuotientPresheaf, CommRingCat.ofHom]
  set m := _
  change Function.Injective (algebraMap _ (Localization m))
  change Function.Injective (algebraMap (F.presheaf.obj U) _)
  haveI : IsLocalization _ (Localization m) := Localization.isLocalization
  refine IsLocalization.injective (M := m) (S := Localization m) ?_
  intro s hs t e
  apply section_ext F (unop U)
  intro x hx
  rw [map_zero]
  apply Submonoid.mem_iInf.mp hs ⟨x, hx⟩
  rw [← map_mul, e, map_zero]
end SubmonoidPresheaf
end TopCat.Presheaf
section ContinuousFunctions
namespace TopCat
variable (X : TopCat.{v})
def continuousFunctions (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v}) : CommRingCat.{v} :=
  @CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R) <|
    inferInstanceAs (CommRing (ContinuousMap _ _))
namespace continuousFunctions
def pullback {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat) :
    continuousFunctions X R ⟶ continuousFunctions Y R where
  toFun g := f.unop ≫ g
  map_one' := rfl
  map_zero' := rfl
  map_add' := by aesop_cat
  map_mul' := by aesop_cat
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S where
  toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
  map_one' := ContinuousMap.ext fun _ => φ.1.map_one
  map_zero' := ContinuousMap.ext fun _ => φ.1.map_zero
  map_add' := fun _ _ => ContinuousMap.ext fun _ => φ.1.map_add _ _
  map_mul' := fun _ _ => ContinuousMap.ext fun _ => φ.1.map_mul _ _
end continuousFunctions
def commRingYoneda : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj R :=
    { obj := fun X => continuousFunctions X R
      map := fun {_ _} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {_ _ _} _ _ => rfl }
  map {_ _} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun _ _ _ => rfl }
  map_id X := by
    ext
    rfl
  map_comp {_ _ _} _ _ := rfl
def presheafToTopCommRing (T : TopCommRingCat.{v}) : X.Presheaf CommRingCat.{v} :=
  (Opens.toTopCat X).op ⋙ commRingYoneda.obj T
end TopCat
end ContinuousFunctions
section Stalks
namespace TopCat.Presheaf
variable {X Y Z : TopCat.{v}}
instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ U x.1 x.2).toAlgebra
@[simp]
theorem stalk_open_algebraMap {X : TopCat} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = F.germ U x.1 x.2 :=
  rfl
end TopCat.Presheaf
end Stalks
noncomputable section Gluing
namespace TopCat.Sheaf
open TopologicalSpace Opposite CategoryTheory
variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}
variable (F : X.Sheaf C) (U V : Opens X)
open CategoryTheory.Limits
def objSupIsoProdEqLocus {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) :
    F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of <|
    RingHom.eqLocus
      (RingHom.comp (F.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
        (RingHom.fst (F.val.obj <| op U) (F.val.obj <| op V)))
      (RingHom.comp (F.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)
        (RingHom.snd (F.val.obj <| op U) (F.val.obj <| op V))) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)
theorem objSupIsoProdEqLocus_hom_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
theorem objSupIsoProdEqLocus_hom_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
theorem objSupIsoProdEqLocus_inv_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x
theorem objSupIsoProdEqLocus_inv_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x
theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W ≤ U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW ≤ U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW ≤ V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    repeat rw [← comp_apply]
    simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (inf_le_right : V ⊓ W ≤ W)) ?_ _ _ ?_ ?_
    · rw [← inf_sup_right]
      exact le_inf e le_rfl
    · rw [← e₁, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]
    · rw [← e₂, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]
end TopCat.Sheaf
end Gluing