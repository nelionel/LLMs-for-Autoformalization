import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Subterminal
universe v₁ v₂ u₁ u₂
noncomputable section
namespace CategoryTheory
open Category
section Ideal
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}
variable (i) [ChosenFiniteProducts C] [CartesianClosed C]
class ExponentialIdeal : Prop where
  exp_closed : ∀ {B}, B ∈ i.essImage → ∀ A, (A ⟹ B) ∈ i.essImage
attribute [nolint docBlame] ExponentialIdeal.exp_closed
theorem ExponentialIdeal.mk' (h : ∀ (B : D) (A : C), (A ⟹ i.obj B) ∈ i.essImage) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((exp A).mapIso iB') (h B' A)⟩
instance : ExponentialIdeal (𝟭 C) :=
  ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩
open CartesianClosed
instance : ExponentialIdeal (subterminalInclusion C) := by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (CartesianClosed.uncurry g) (CartesianClosed.uncurry h))
def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ exp A ⋙ reflector i ⋙ i ≅ i ⋙ exp A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]
theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : ∀ A : C, i ⋙ exp A ⋙ reflector i ⋙ i ≅ i ⋙ exp A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩
end Ideal
section
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]
variable (i : D ⥤ C)
theorem reflective_products [Limits.HasFiniteProducts C] [Reflective i] :
    Limits.HasFiniteProducts D := ⟨fun _ => hasLimitsOfShape_of_reflective i⟩
open CartesianClosed MonoidalCategory ChosenFiniteProducts
open Limits in
def reflectiveChosenFiniteProducts [ChosenFiniteProducts C] [Reflective i] :
    ChosenFiniteProducts D where
  product X Y :=
    { cone := BinaryFan.mk
        ((reflector i).map (fst (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
        ((reflector i).map (snd (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
      isLimit := by
        apply isLimitOfReflects i
        apply IsLimit.equivOfNatIsoOfIso (pairComp X Y _) _ _ _|>.invFun
          (product (i.obj X) (i.obj Y)).isLimit
        fapply BinaryFan.ext
        · change (reflector i ⋙ i).obj (i.obj X ⊗ i.obj Y) ≅ (𝟭 C).obj (i.obj X ⊗ i.obj Y)
          letI : IsIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) := by
            apply Functor.essImage.unit_isIso
            haveI := reflective_products i
            use Limits.prod X Y
            constructor
            apply Limits.PreservesLimitPair.iso i _ _|>.trans
            refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (i.obj X) (i.obj Y)))
              (ChosenFiniteProducts.product _ _).isLimit
          exact asIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y))|>.symm
        · simp only [BinaryFan.fst, Cones.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc, fst]
        · simp only [BinaryFan.snd, Cones.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc, snd] }
  terminal :=
    { cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
      isLimit := by
        apply isLimitOfReflects i
        apply isLimitChangeEmptyCone _ ChosenFiniteProducts.terminal.isLimit
        letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
          apply Functor.essImage.unit_isIso
          haveI := reflective_products i
          use Limits.terminal D
          constructor
          apply Limits.PreservesTerminal.iso i|>.trans
          refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _)
            (ChosenFiniteProducts.terminal).isLimit
        exact asIso ((reflectorAdjunction i).unit.app (𝟙_ C)) }
variable [ChosenFiniteProducts C] [Reflective i] [CartesianClosed C] [ChosenFiniteProducts D]
instance (priority := 10) exponentialIdeal_of_preservesBinaryProducts
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (reflector i)] :
    ExponentialIdeal i := by
  let ir := reflectorAdjunction i
  let L : C ⥤ D := reflector i
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit
  apply ExponentialIdeal.mk'
  intro B A
  let q : i.obj (L.obj (A ⟹ i.obj B)) ⟶ A ⟹ i.obj B := by
    apply CartesianClosed.curry (ir.homEquiv _ _ _)
    apply _ ≫ (ir.homEquiv _ _).symm ((exp.ev A).app (i.obj B))
    exact prodComparison L A _ ≫ (_ ◁ (ε.app _)) ≫ inv (prodComparison _ _ _)
  have : η.app (A ⟹ i.obj B) ≫ q = 𝟙 (A ⟹ i.obj B) := by
    dsimp
    rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← ir.homEquiv_naturality_left,
      ir.homEquiv_apply_eq, assoc, assoc, prodComparison_natural_whiskerLeft_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ir.left_triangle_components, MonoidalCategory.whiskerLeft_id, id_comp]
    apply IsIso.hom_inv_id_assoc
  haveI : IsSplitMono (η.app (A ⟹ i.obj B)) := IsSplitMono.mk' ⟨_, this⟩
  apply mem_essImage_of_unit_isSplitMono
variable [ExponentialIdeal i]
def cartesianClosedOfReflective : CartesianClosed D where
  closed := fun B =>
    { rightAdj := i ⋙ exp (i.obj B) ⋙ reflector i
      adj := by
        apply (exp.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm
          refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
          · haveI :=
              Adjunction.rightAdjoint_preservesLimits.{0, 0} (reflectorAdjunction i)
            apply asIso (prodComparison i B X)
          · dsimp [asIso]
            rw [prodComparison_natural_whiskerLeft]
        · apply (exponentialIdealReflective i _).symm }
attribute [-instance] CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit
  CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
noncomputable def bijection (A B : C) (X : D) :
    ((reflector i).obj (A ⊗ B) ⟶ X) ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
  calc
    _ ≃ (A ⊗ B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B ⊗ A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (exp.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (B ⊗ i.obj ((reflector i).obj A) ⟶ i.obj X) := ((exp.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A) ⊗ B ⟶ i.obj X) :=
      ((β_ _ _).homCongr (Iso.refl _))
    _ ≃ (B ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) := (exp.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj B) ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (i.obj ((reflector i).obj A) ⊗ i.obj ((reflector i).obj B) ⟶ i.obj X) :=
      ((exp.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A ⊗ (reflector i).obj B) ⟶ i.obj X) :=
      haveI : Limits.PreservesLimits i := (reflectorAdjunction i).rightAdjoint_preservesLimits
      haveI := Limits.preservesSmallestLimits_of_preservesLimits i
      Iso.homCongr (prodComparisonIso _ _ _).symm (Iso.refl (i.obj X))
    _ ≃ ((reflector i).obj A ⊗ (reflector i).obj B ⟶ X) :=
      i.fullyFaithfulOfReflective.homEquiv.symm
theorem bijection_symm_apply_id (A B : C) :
    (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _ := by
  dsimp [bijection]
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  rw [comp_id, comp_id, comp_id, i.map_id, comp_id, unitCompPartialBijective_symm_apply,
    unitCompPartialBijective_symm_apply, uncurry_natural_left, uncurry_curry,
    uncurry_natural_left, uncurry_curry, ← BraidedCategory.braiding_naturality_left_assoc]
  erw [SymmetricCategory.symmetry_assoc, ← MonoidalCategory.whisker_exchange_assoc]
  dsimp only [Functor.comp_obj]
  rw [← tensorHom_def'_assoc, Adjunction.homEquiv_symm_apply,
    ← Adjunction.eq_unit_comp_map_iff, Iso.comp_inv_eq, assoc]
  rw [prodComparisonIso_hom i ((reflector i).obj A) ((reflector i).obj B)]
  apply hom_ext
  · rw [tensorHom_fst, assoc, assoc, prodComparison_fst, ← i.map_comp,
    prodComparison_fst]
    apply (reflectorAdjunction i).unit.naturality
  · rw [tensorHom_snd, assoc, assoc, prodComparison_snd, ← i.map_comp,
    prodComparison_snd]
    apply (reflectorAdjunction i).unit.naturality
theorem bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A ⊗ B) ⟶ X) (g : X ⟶ X') :
    bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g := by
  dsimp [bijection]
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage, i.map_comp,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [comp_id, Functor.map_comp, Functor.FullyFaithful.map_preimage, assoc]
  rw [← assoc, ← assoc, curry_natural_right _ (i.map g),
    unitCompPartialBijective_natural, uncurry_natural_right, ← assoc, curry_natural_right,
    unitCompPartialBijective_natural, uncurry_natural_right, assoc]
theorem prodComparison_iso (A B : C) : IsIso
    (prodComparison (reflector i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply, id_comp],
      by rw [← bijection_natural, id_comp, ← bijection_symm_apply_id, Equiv.apply_symm_apply]⟩⟩
attribute [local instance] prodComparison_iso
open Limits
lemma preservesBinaryProducts_of_exponentialIdeal :
    PreservesLimitsOfShape (Discrete WalkingPair) (reflector i) where
  preservesLimit {K} :=
    letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm
lemma preservesFiniteProducts_of_exponentialIdeal (J : Type) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) (reflector i) := by
  letI := preservesBinaryProducts_of_exponentialIdeal i
  letI : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  apply preservesFiniteProducts_of_preserves_binary_and_terminal (reflector i) J
end
end CategoryTheory