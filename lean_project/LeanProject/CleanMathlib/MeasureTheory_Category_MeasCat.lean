import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.Topology.Category.TopCat.Basic
noncomputable section
open CategoryTheory MeasureTheory
open scoped ENNReal
universe u v
def MeasCat : Type (u + 1) :=
  Bundled MeasurableSpace
namespace MeasCat
instance : CoeSort MeasCat Type* :=
  Bundled.coeSort
instance (X : MeasCat) : MeasurableSpace X :=
  X.str
def of (α : Type u) [ms : MeasurableSpace α] : MeasCat :=
  ⟨α, ms⟩
@[simp]
theorem coe_of (X : Type u) [MeasurableSpace X] : (of X : Type u) = X :=
  rfl
instance unbundledHom : UnbundledHom @Measurable :=
  ⟨@measurable_id, @Measurable.comp⟩
deriving instance LargeCategory for MeasCat
instance : ConcreteCategory MeasCat := by
  unfold MeasCat
  infer_instance
instance : Inhabited MeasCat :=
  ⟨MeasCat.of Empty⟩
attribute [local instance] ConcreteCategory.instFunLike
def Measure : MeasCat ⥤ MeasCat where
  obj X := ⟨@MeasureTheory.Measure X.1 X.2, inferInstance⟩
  map f := ⟨Measure.map (⇑f), Measure.measurable_map f.1 f.2⟩
  map_id := fun ⟨α, I⟩ => Subtype.eq <| funext fun μ => @Measure.map_id α I μ
  map_comp := fun ⟨_, hf⟩ ⟨_, hg⟩ => Subtype.eq <| funext fun _ => (Measure.map_map hg hf).symm
def Giry : CategoryTheory.Monad MeasCat where
  toFunctor := Measure
  η :=
    { app := fun X => ⟨@Measure.dirac X.1 X.2, Measure.measurable_dirac⟩
      naturality := fun _ _ ⟨_, hf⟩ => Subtype.eq <| funext fun a => (Measure.map_dirac hf a).symm }
  μ :=
    { app := fun X => ⟨@Measure.join X.1 X.2, Measure.measurable_join⟩
      naturality := fun _ _ ⟨_, hf⟩ => Subtype.eq <| funext fun μ => Measure.join_map_map hf μ }
  assoc _ := Subtype.eq <| funext fun _ => Measure.join_map_join _
  left_unit _ := Subtype.eq <| funext fun _ => Measure.join_dirac _
  right_unit _ := Subtype.eq <| funext fun _ => Measure.join_map_dirac _
def Integral : Giry.Algebra where
  A := MeasCat.of ℝ≥0∞
  a := ⟨fun m : MeasureTheory.Measure ℝ≥0∞ ↦ ∫⁻ x, x ∂m, Measure.measurable_lintegral measurable_id⟩
  unit := Subtype.eq <| funext fun _ : ℝ≥0∞ => lintegral_dirac' _ measurable_id
  assoc := Subtype.eq <| funext fun μ : MeasureTheory.Measure (MeasureTheory.Measure ℝ≥0∞) =>
    show ∫⁻ x, x ∂μ.join = ∫⁻ x, x ∂Measure.map (fun m => ∫⁻ x, x ∂m) μ by
      rw [Measure.lintegral_join, lintegral_map] <;>
        apply_rules [measurable_id, Measure.measurable_lintegral]
end MeasCat
instance TopCat.hasForgetToMeasCat : HasForget₂ TopCat.{u} MeasCat.{u} :=
  BundledHom.mkHasForget₂ borel (fun f => ⟨f.1, f.2.borel_measurable⟩) (fun _ => rfl)
abbrev Borel : TopCat.{u} ⥤ MeasCat.{u} :=
  forget₂ TopCat.{u} MeasCat.{u}