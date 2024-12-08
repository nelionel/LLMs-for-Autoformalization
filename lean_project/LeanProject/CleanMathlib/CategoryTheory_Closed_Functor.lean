import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
noncomputable section
namespace CategoryTheory
open Category CartesianClosed MonoidalCategory ChosenFiniteProducts
universe v u u'
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]
variable [ChosenFiniteProducts C] [ChosenFiniteProducts D]
variable (F : C ⥤ D) {L : D ⥤ C}
def frobeniusMorphism (h : L ⊣ F) (A : C) :
    tensorLeft (F.obj A) ⋙ L ⟶ L ⋙ tensorLeft A :=
  prodComparisonNatTrans L (F.obj A) ≫ whiskerLeft _ ((curriedTensor C).map (h.counit.app _))
instance frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] [F.Full] [F.Faithful] :
    IsIso (frobeniusMorphism F h A) :=
  suffices ∀ (X : D), IsIso ((frobeniusMorphism F h A).app X) from NatIso.isIso_of_isIso_app _
  fun B ↦ by dsimp [frobeniusMorphism]; infer_instance
variable [CartesianClosed C] [CartesianClosed D]
variable [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]
def expComparison (A : C) : exp A ⋙ F ⟶ F ⋙ exp (F.obj A) :=
  mateEquiv (exp.adjunction A) (exp.adjunction (F.obj A)) (prodComparisonNatIso F A).inv
theorem expComparison_ev (A B : C) :
    F.obj A ◁ ((expComparison F A).app B) ≫ (exp.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  convert mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id 
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, asIso_inv, NatIso.isIso_inv_app,
    IsIso.hom_inv_id]
theorem coev_expComparison (A B : C) :
    F.map ((exp.coev A).app B) ≫ (expComparison F A).app (A ⊗ B) =
      (exp.coev _).app (F.obj B) ≫ (exp (F.obj A)).map (inv (prodComparison F A B)) := by
  convert unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id 
  dsimp
  simp
theorem uncurry_expComparison (A B : C) :
    CartesianClosed.uncurry ((expComparison F A).app B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  rw [uncurry_eq, expComparison_ev]
theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    expComparison F A ≫ whiskerLeft _ (pre (F.map f)) =
      whiskerRight (pre f) _ ≫ expComparison F A' := by
  unfold expComparison pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (exp.adjunction A) (exp.adjunction (F.obj A)) (exp.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (exp.adjunction A) (exp.adjunction A') (exp.adjunction (F.obj A'))
    (((curriedTensor C).map f)) ((prodComparisonNatIso F A').inv)
  unfold leftAdjointSquareConjugate.vcomp rightAdjointSquareConjugate.vcomp at vcomp1
  unfold leftAdjointConjugateSquare.vcomp rightAdjointConjugateSquare.vcomp at vcomp2
  rw [← vcomp1, ← vcomp2]
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, tensorLeft_obj, prodComparisonNatIso_inv, asIso_inv,
    NatTrans.comp_app, whiskerLeft_app, curriedTensor_map_app, NatIso.isIso_inv_app,
    whiskerRight_app, IsIso.eq_inv_comp, prodComparisonNatTrans_app]
  rw [← prodComparison_inv_natural_whiskerRight F f]
  simp
class CartesianClosedFunctor : Prop where
  comparison_iso : ∀ A, IsIso (expComparison F A)
attribute [instance] CartesianClosedFunctor.comparison_iso
theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    conjugateEquiv (h.comp (exp.adjunction A)) ((exp.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A) =
      expComparison F A := by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (exp.adjunction (F.obj A)) (exp.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫ whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  apply congr_arg
  ext B
  unfold mateEquiv
  simp only [Functor.comp_obj, tensorLeft_obj, Functor.id_obj, Equiv.coe_fn_mk, whiskerLeft_comp,
    whiskerLeft_twice, whiskerRight_comp, assoc, NatTrans.comp_app, whiskerLeft_app,
    curriedTensor_obj_obj, whiskerRight_app, prodComparisonNatTrans_app, curriedTensor_map_app,
    Functor.comp_map, tensorLeft_map, prodComparisonNatIso_inv, asIso_inv, NatIso.isIso_inv_app]
  rw [← F.map_comp, ← F.map_comp]
  simp only [Functor.map_comp]
  apply IsIso.eq_inv_of_inv_hom_id
  simp only [assoc]
  rw [prodComparison_natural_whiskerLeft, prodComparison_natural_whiskerRight_assoc]
  slice_lhs 2 3 => rw [← prodComparison_comp]
  simp only [assoc]
  unfold prodComparison
  have ηlemma : (h.unit.app (F.obj A ⊗ F.obj B) ≫
    lift ((L ⋙ F).map (fst _ _)) ((L ⋙ F).map (snd _ _))) =
      (h.unit.app (F.obj A)) ⊗ (h.unit.app (F.obj B)) := by
    ext <;> simp
  slice_lhs 1 2 => rw [ηlemma]
  simp only [Functor.id_obj, Functor.comp_obj, assoc, ← whisker_exchange, ← tensorHom_def']
  ext <;> simp
theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A)] : IsIso (frobeniusMorphism F h A) := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i
theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A) := by
  rw [← frobeniusMorphism_mate F h]; infer_instance
open Limits in
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : CartesianClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _
end CategoryTheory