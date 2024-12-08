import Mathlib.Condensed.Discrete.Basic
import Mathlib.Condensed.TopComparison
import Mathlib.Topology.Category.CompHausLike.SigmaComparison
import Mathlib.Topology.FiberPartition
universe u w
open CategoryTheory Limits LocallyConstant TopologicalSpace.Fiber Opposite Function Fiber
attribute [local instance] ConcreteCategory.instFunLike
variable {P : TopCat.{u} → Prop}
namespace CompHausLike.LocallyConstant
@[simps]
def functorToPresheaves : Type (max u w) ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) where
  obj X := {
    obj := fun ⟨S⟩ ↦ LocallyConstant S X
    map := fun f g ↦ g.comap f.unop }
  map f := { app := fun _ t ↦ t.map f }
@[simps]
def locallyConstantIsoContinuousMap (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := fun f ↦ (f : C(Y, X))
    inv := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }
section Adjunction
variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]
section
variable {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : Fiber r)
def fiber : CompHausLike.{u} P := CompHausLike.of P a.val
instance : HasProp P (fiber r a) := inferInstanceAs (HasProp P (Subtype _))
def sigmaIncl : fiber r a ⟶ Q := TopologicalSpace.Fiber.sigmaIncl _ a
noncomputable def sigmaIso [HasExplicitFiniteCoproducts.{u} P] : (finiteCoproduct (fiber r)) ≅ Q :=
  isoOfBijective (sigmaIsoHom r) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩
lemma sigmaComparison_comp_sigmaIso [HasExplicitFiniteCoproducts.{u} P]
    (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) :
    (X.mapIso (sigmaIso r).op).hom ≫ sigmaComparison X (fun a ↦ (fiber r a).1) ≫
      (fun g ↦ g a) = X.map (sigmaIncl r a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, sigmaComparison, coe_of,
    ← FunctorToTypes.map_comp_apply]
  rfl
end
variable {S : CompHausLike.{u} P} {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w}
  [HasProp P PUnit.{u+1}] (f : LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u+1}))))
noncomputable def counitAppAppImage : (a : Fiber f) → Y.obj ⟨fiber f a⟩ :=
  fun a ↦ Y.map (CompHausLike.isTerminalPUnit.from _).op a.image
noncomputable def counitAppApp (S : CompHausLike.{u} P) (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P] :
    LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u+1}))) ⟶ Y.obj ⟨S⟩ :=
  fun r ↦ ((inv (sigmaComparison Y (fun a ↦ (fiber r a).1))) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)
lemma presheaf_ext (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩)
    [HasExplicitFiniteCoproducts.{u} P]
    (h : ∀ (a : Fiber f), X.map (sigmaIncl f a).op x = X.map (sigmaIncl f a).op y) : x = y := by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a ↦ (fiber f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h
lemma incl_of_counitAppApp [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P]
    (a : Fiber f) : Y.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  rw [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, types_comp_apply,
    ← FunctorToTypes.map_comp_apply, Iso.inv_hom_id, FunctorToTypes.map_id_apply]
  exact congrFun (inv_hom_id_apply (asIso (sigmaComparison Y (fun a ↦ (fiber f a).1)))
    (counitAppAppImage f)) _
variable {T : CompHausLike.{u} P} (g : T ⟶ S)
def componentHom (a : Fiber (f.comap g)) :
    fiber _ a ⟶ fiber _ (Fiber.mk f (g a.preimage)) where
  toFun x := ⟨g x.val, by
    simp only [Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff]
    convert map_eq_image _ _ x
    exact map_preimage_eq_image_map _ _ a⟩
  continuous_toFun := by exact Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _
lemma incl_comap {S T : (CompHausLike P)ᵒᵖ}
    (f : LocallyConstant S.unop (Y.obj (op (CompHausLike.of P PUnit.{u+1}))))
      (g : S ⟶ T) (a : Fiber (f.comap g.unop)) :
        g ≫ (sigmaIncl (f.comap g.unop) a).op =
          (sigmaIncl f _).op ≫ (componentHom f g.unop a).op :=
  rfl
@[simps!]
noncomputable def counitApp [HasExplicitFiniteCoproducts.{u} P]
    (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) [PreservesFiniteProducts Y] :
    (functorToPresheaves.obj (Y.obj (op (CompHausLike.of P PUnit.{u+1})))) ⟶ Y where
  app := fun ⟨S⟩ ↦ counitAppApp S Y
  naturality := by
    intro S T g
    ext f
    apply presheaf_ext (f.comap g.unop)
    intro a
    simp only [op_unop, functorToPresheaves_obj_obj, types_comp_apply, functorToPresheaves_obj_map,
      incl_of_counitAppApp, ← FunctorToTypes.map_comp_apply, incl_comap]
    simp only [FunctorToTypes.map_comp_apply, incl_of_counitAppApp]
    simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
      terminal.comp_from]
    apply congrArg
    exact image_eq_image_mk (g := g.unop) (a := a)
variable (P) (X : TopCat.{max u w})
    [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)
noncomputable def functorToPresheavesIso (X : Type (max u w)) :
    functorToPresheaves.{u, w}.obj X ≅ ((TopCat.discrete.obj X).toSheafCompHausLike P hs).val :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)
@[simps]
def functor :
    haveI := CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := {
    val := functorToPresheaves.{u, w}.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIso P hs X)]
      exact ((TopCat.discrete.obj X).toSheafCompHausLike P hs).cond }
  map f := ⟨functorToPresheaves.{u, w}.map f⟩
noncomputable def functorIso :
    functor.{u, w} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))
@[simps]
noncomputable def counit [HasExplicitFiniteCoproducts.{u} P] : haveI := CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X := haveI := CompHausLike.preregular hs
    ⟨counitApp X.val⟩
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply Sheaf.hom_ext
    simp only [functor, id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Sheaf.instCategorySheaf_comp_val, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_app]
    apply presheaf_ext (f.map (g.val.app (op (CompHausLike.of P PUnit.{u+1}))))
    intro a
    simp only [op_unop, functorToPresheaves_map_app, incl_of_counitAppApp]
    apply presheaf_ext (f.comap (sigmaIncl _ _))
    intro b
    simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp, CompHausLike.coe_of,
      map_apply, IsTerminal.comp_from, ← map_preimage_eq_image_map]
    change (_ ≫ Y.val.map _) _ = (_ ≫ Y.val.map _) _
    simp only [← g.val.naturality,
      show sigmaIncl (f.comap (sigmaIncl (f.map _) a)) b ≫ sigmaIncl (f.map _) a =
        (sigmaInclIncl f _ a b) ≫ sigmaIncl f (Fiber.mk f _) from rfl]
    simp only [op_comp, Functor.map_comp, types_comp_apply, incl_of_counitAppApp]
    simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp, terminal.comp_from]
    rw [mk_image]
    change (X.val.map _ ≫ _) _ = (X.val.map _ ≫ _) _
    simp only [g.val.naturality]
    simp only [types_comp_apply]
    have := map_preimage_eq_image (f := g.val.app _ ∘ f) (a := a)
    simp only [Function.comp_apply] at this
    rw [this]
    apply congrArg
    symm
    convert (b.preimage).prop
    exact (mem_iff_eq_image (g.val.app _ ∘ f) _ _).symm
@[simps]
def unit : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  app _ x := LocallyConstant.const _ x
noncomputable def unitIso : 𝟭 (Type max u w) ≅ functor.{u, w} P hs ⋙
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  hom := unit P hs
  inv := { app := fun _ f ↦ f.toFun PUnit.unit }
lemma adjunction_left_triangle [HasExplicitFiniteCoproducts.{u} P]
    (X : Type max u w) : functorToPresheaves.{u, w}.map ((unit P hs).app X) ≫
      ((counit P hs).app ((functor P hs).obj X)).val = 𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, FunctorToTypes.comp, NatTrans.id_app,
    functorToPresheaves_obj_obj, types_id_apply]
  simp only [counit, counitApp_app]
  have := CompHausLike.preregular hs
  apply presheaf_ext
    (X := ((functor P hs).obj X).val) (Y := ((functor.{u, w} P hs).obj X).val)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_val, functorToPresheaves_obj_obj, coe_of, Functor.id_obj,
    counitAppAppImage, LocallyConstant.map_apply, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← map_eq_image _ a x]
  rfl
@[simps]
noncomputable def adjunction [HasExplicitFiniteCoproducts.{u} P] :
    functor.{u, w} P hs ⊣ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  unit := unit P hs
  counit := counit P hs
  left_triangle_components := by
    intro X
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.flip_obj_obj,
      sheafToPresheaf_obj, functor_obj_val, functorToPresheaves_obj_obj, coe_of, whiskerRight_app,
      Functor.associator_hom_app, whiskerLeft_app, Category.id_comp, NatTrans.id_app']
    apply Sheaf.hom_ext
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_id_val]
    exact adjunction_left_triangle P hs X
  right_triangle_components := by
    intro X
    ext (x : X.val.obj _)
    simp only [Functor.comp_obj, Functor.id_obj, Functor.flip_obj_obj, sheafToPresheaf_obj,
      FunctorToTypes.comp, whiskerLeft_app, unit_app, coe_of, Functor.associator_inv_app,
      functor_obj_val, functorToPresheaves_obj_obj, types_id_apply, whiskerRight_app,
      Functor.flip_obj_map, sheafToPresheaf_map, counit_app_val, counitApp_app, NatTrans.id_app']
    have := CompHausLike.preregular hs
    letI : PreservesFiniteProducts ((sheafToPresheaf (coherentTopology _) _).obj X) :=
      inferInstanceAs (PreservesFiniteProducts (Sheaf.val _))
    apply presheaf_ext ((unit P hs).app _ x)
    intro a
    erw [incl_of_counitAppApp]
    simp only [sheafToPresheaf_obj, unit_app, coe_of, counitAppAppImage, coe_const]
    erw [← map_eq_image _ a ⟨PUnit.unit, by simp [mem_iff_eq_image, ← map_preimage_eq_image]⟩]
    rfl
instance [HasExplicitFiniteCoproducts.{u} P] : IsIso (adjunction P hs).unit :=
  inferInstanceAs (IsIso (unitIso P hs).hom)
end Adjunction
end CompHausLike.LocallyConstant
section Condensed
open Condensed CompHausLike
namespace CondensedSet.LocallyConstant
abbrev functor : Type (u+1) ⥤ CondensedSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u+1} (P := fun _ ↦ True)
    (hs := fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)
noncomputable def iso : functor ≅ discrete (Type (u+1)) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)
noncomputable def functorFullyFaithful : functor.FullyFaithful :=
  (LocallyConstant.adjunction.{u, u+1} _ _).fullyFaithfulLOfIsIsoUnit
noncomputable instance : functor.Faithful := functorFullyFaithful.faithful
noncomputable instance : functor.Full := functorFullyFaithful.full
instance : (discrete (Type _)).Faithful := Functor.Faithful.of_iso iso
noncomputable instance : (discrete (Type _)).Full := Functor.Full.of_iso iso
end CondensedSet.LocallyConstant
namespace LightCondSet.LocallyConstant
abbrev functor : Type u ⥤ LightCondSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u}
    (P := fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)
instance (S : LightProfinite.{u}) (p : S → Prop) :
    HasProp (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X) (Subtype p) :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace (Subtype p)),
    (inferInstance : SecondCountableTopology {s | p s})⟩⟩
noncomputable def iso : functor ≅ LightCondensed.discrete (Type u) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)
noncomputable def functorFullyFaithful : functor.{u}.FullyFaithful :=
  (LocallyConstant.adjunction _ _).fullyFaithfulLOfIsIsoUnit
instance : functor.{u}.Faithful := functorFullyFaithful.faithful
instance : LightCondSet.LocallyConstant.functor.Full := functorFullyFaithful.full
instance : (LightCondensed.discrete (Type u)).Faithful := Functor.Faithful.of_iso iso.{u}
instance : (LightCondensed.discrete (Type u)).Full := Functor.Full.of_iso iso.{u}
end LightCondSet.LocallyConstant
end Condensed