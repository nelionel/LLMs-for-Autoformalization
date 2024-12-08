import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Products
universe w w' v u
open CategoryTheory Opposite Limits
variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) (Y : Type w') [TopologicalSpace Y]
namespace ContinuousMap
@[simps]
def yonedaPresheaf : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)
@[simps]
def yonedaPresheaf' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  obj X := C((unop X).1, Y)
  map f g := ContinuousMap.comp g f.unop
theorem comp_yonedaPresheaf' : yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y := rfl
theorem piComparison_fac {α : Type} (X : α → TopCat) :
    piComparison (yonedaPresheaf'.{w, w'} Y) (fun x ↦ op (X x)) =
    (yonedaPresheaf' Y).map ((opCoproductIsoProduct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫
    (equivEquivIso (sigmaEquiv Y (fun x ↦ (X x).1))).inv ≫ (Types.productIso _).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  ext
  simp only [yonedaPresheaf', unop_op, piComparison, types_comp_apply,
    Types.productIso_hom_comp_eval_apply, Types.pi_lift_π_apply, comp_apply, TopCat.coe_of,
    unop_comp, Quiver.Hom.unop_op, sigmaEquiv, equivEquivIso_hom, Equiv.toIso_inv,
    Equiv.coe_fn_symm_mk, comp_assoc, sigmaMk_apply, ← opCoproductIsoProduct_inv_comp_ι]
  rfl
noncomputable instance : PreservesFiniteProducts (yonedaPresheaf'.{w, w'} Y) where
  preserves _ _ :=
    { preservesLimit := fun {K} =>
      have : ∀ {α : Type} (X : α → TopCat), PreservesLimit (Discrete.functor (fun x ↦ op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.of_iso_comparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x ↦ op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i ↦ op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimit_of_iso_diagram _ i.symm }
end ContinuousMap