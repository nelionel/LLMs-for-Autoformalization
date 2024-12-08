import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.TransferInstance
universe u₁ u₂ v₁ v₂ w t
namespace CategoryTheory
open Limits Functor
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  hasTerminal : HasTerminal C := by infer_instance
  hasPullbacks : HasPullbacks C := by infer_instance
  hasFiniteCoproducts : HasFiniteCoproducts C := by infer_instance
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))
namespace PreGaloisCategory
class FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F := by
    infer_instance
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  preservesFiniteCoproducts : PreservesFiniteCoproducts F := by infer_instance
  preservesEpis : Functor.PreservesEpimorphisms F := by infer_instance
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
  reflectsIsos : F.ReflectsIsomorphisms := by infer_instance
class IsConnected {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i
class PreservesIsConnected {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  preserves : ∀ {X : C} [IsConnected X], IsConnected (F.obj X)
section
variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups
instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products
instance {G : Type*} [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm
end
namespace FiberFunctor
variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FiberFunctor F]
attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups
noncomputable instance : ReflectsLimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms
noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms
noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
instance {G : Type*} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by
  choose G' hg hf he using Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv he.some.toSingleObjEquiv.symm F
instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk <| by
  intro X Y f _
  haveI : IsIso (pullback.fst (F.map f) (F.map f)) :=
    isIso_fst_of_mono (F.map f)
  haveI : IsIso (F.map (pullback.fst f f)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  haveI : IsIso (pullback.fst f f) := isIso_of_reflects_iso (pullback.fst _ _) F
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst
instance : F.Faithful where
  map_injective {X Y} f g h := by
    haveI : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    haveI : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    haveI : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer
section
lemma comp_right (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.IsEquivalence] :
    FiberFunctor (F ⋙ E) where
  preservesQuotientsByFiniteGroups _ := comp_preservesColimitsOfShape F E
end
end FiberFunctor
variable {C : Type u₁} [Category.{u₂, u₁} C]
  (F : C ⥤ FintypeCat.{w})
instance (X : C) : MulAction (Aut F) (F.obj X) where
  smul σ x := σ.hom.app X x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
lemma mulAction_def {X : C} (σ : Aut F) (x : F.obj X) :
    σ • x = σ.hom.app X x :=
  rfl
lemma mulAction_naturality {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) :
    σ • F.map f x = F.map f (σ • x) :=
  FunctorToFintypeCat.naturality F F σ.hom f x
lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : ¬ IsConnected X)
    (hi : IsInitial X → False) :
    ∃ (Y : C) (v : Y ⟶ X), (IsInitial Y → False) ∧ Mono v ∧ (¬ IsIso v) := by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni ↦ hc Y i hni hm⟩
lemma card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)
variable [PreGaloisCategory C] [FiberFunctor F]
lemma initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  haveI : PreservesFiniteColimits (forget FintypeCat) := by
    show PreservesFiniteColimits FintypeCat.incl
    infer_instance
  haveI : ReflectsColimit (Functor.empty.{0} _) (forget FintypeCat) := by
    show ReflectsColimit (Functor.empty.{0} _) FintypeCat.incl
    infer_instance
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)
lemma not_initial_iff_fiber_nonempty (X : C) : (IsInitial X → False) ↔ Nonempty (F.obj X) := by
  rw [← not_isEmpty_iff]
  refine ⟨fun h he ↦ ?_, fun h hin ↦ h <| (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h
lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x
instance nonempty_fiber_of_isConnected (X : C) [IsConnected X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin
noncomputable def fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
  Types.equalizerIso (F.map f) (F.map g)).toEquiv
@[simp]
lemma fiberEqualizerEquiv_symm_ι_apply {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
    (h : F.map f x = F.map g x) :
    F.map (equalizer.ι f g) ((fiberEqualizerEquiv F f g).symm ⟨x, h⟩) = x := by
  simp [fiberEqualizerEquiv]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]
noncomputable def fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 } :=
  (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
  Types.pullbackIsoPullback (F.map f) (F.map g)).toEquiv
@[simp]
lemma fiberPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.fst f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = a := by
  simp [fiberPullbackEquiv]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]
@[simp]
lemma fiberPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.snd f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = b := by
  simp [fiberPullbackEquiv]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]
noncomputable def fiberBinaryProductEquiv (X Y : C) :
    F.obj (X ⨯ Y) ≃ F.obj X × F.obj Y :=
  (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv
@[simp]
lemma fiberBinaryProductEquiv_symm_fst_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.fst ((fiberBinaryProductEquiv F X Y).symm (x, y)) = x := by
  simp only [fiberBinaryProductEquiv, comp_obj, FintypeCat.incl_obj, Iso.toEquiv_comp,
    Equiv.symm_trans_apply, Iso.toEquiv_symm_fun]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]
@[simp]
lemma fiberBinaryProductEquiv_symm_snd_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.snd ((fiberBinaryProductEquiv F X Y).symm (x, y)) = y := by
  simp only [fiberBinaryProductEquiv, comp_obj, FintypeCat.incl_obj, Iso.toEquiv_comp,
    Equiv.symm_trans_apply, Iso.toEquiv_symm_fun]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]
lemma evaluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun (f : A ⟶ X) ↦ F.map f a) := by
  intro f g (h : F.map f a = F.map g a)
  haveI : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer
lemma evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun f : Aut A ↦ F.map (f.hom) a) := by
  show Function.Injective ((fun f : A ⟶ A ↦ F.map f a) ∘ (fun f : Aut A ↦ f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A
lemma epi_of_nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.obj X)]
    (f : X ⟶ A) : Epi f := Epi.mk <| fun {Z} u v huv ↦ by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using congr_fun (F.congr_map huv) _
lemma surjective_on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f) :=
  surjective_of_epi (FintypeCat.incl.map (F.map f))
lemma surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
    [IsConnected A] (f : X ⟶ A) :
    Function.Surjective (F.map f) := by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f
instance nonempty_fiber_pi_of_nonempty_of_finite {ι : Type*} [Finite ι] (X : ι → C)
    [∀ i, Nonempty (F.obj (X i))] : Nonempty (F.obj (∏ᶜ X)) := by
  cases nonempty_fintype ι
  let f (i : ι) : FintypeCat.{w} := F.obj (X i)
  let i : F.obj (∏ᶜ X) ≅ ∏ᶜ f := PreservesProduct.iso F _
  exact Nonempty.elim inferInstance fun x : (∏ᶜ f : FintypeCat.{w}) ↦ ⟨i.inv x⟩
section CardFiber
open ConcreteCategory
lemma isIso_of_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : Nat.card (F.obj X) = Nat.card (F.obj Y)) : IsIso f := by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflects_iso f F
lemma lt_card_fiber_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : ¬ IsIso f) : Nat.card (F.obj X) < Nat.card (F.obj Y) := by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [gt_iff_lt, not_lt] at hlt
  exact Nat.le_antisymm
    (Finite.card_le_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt
lemma non_zero_card_fiber_of_not_initial (X : C) (h : IsInitial X → False) :
    Nat.card (F.obj X) ≠ 0 := by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero
lemma card_fiber_coprod_eq_sum (X Y : C) :
    Nat.card (F.obj (X ⨿ Y)) = Nat.card (F.obj X) + Nat.card (F.obj Y) := by
  let e : F.obj (X ⨿ Y) ≃ F.obj X ⊕ F.obj Y := Iso.toEquiv
    <| (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
    <| Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective e)
lemma card_hom_le_card_fiber_of_connected (A X : C) [IsConnected A] :
    Nat.card (A ⟶ X) ≤ Nat.card (F.obj X) := by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)
lemma card_aut_le_card_fiber_of_connected (A : C) [IsConnected A] :
    Nat.card (Aut A) ≤ Nat.card (F.obj A) := by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a
end CardFiber
end PreGaloisCategory
class GaloisCategory (C : Type u₁) [Category.{u₂, u₁} C]
    extends PreGaloisCategory C : Prop where
  hasFiberFunctor : ∃ F : C ⥤ FintypeCat.{u₂}, Nonempty (PreGaloisCategory.FiberFunctor F)
namespace PreGaloisCategory
variable (C : Type u₁) [Category.{u₂, u₁} C] [GaloisCategory C]
noncomputable def GaloisCategory.getFiberFunctor : C ⥤ FintypeCat.{u₂} :=
  Classical.choose <| @GaloisCategory.hasFiberFunctor C _ _
noncomputable instance : FiberFunctor (GaloisCategory.getFiberFunctor C) :=
  Classical.choice <| Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)
variable {C}
instance (A X : C) [IsConnected A] : Finite (A ⟶ X) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f a)
  exact evaluation_injective_of_isConnected F A X a
instance (A : C) [IsConnected A] : Finite (Aut A) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f.hom a)
  exact evaluation_aut_injective_of_isConnected F A a
instance : MonoCoprod C := by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F
end PreGaloisCategory
end CategoryTheory