import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
@[mk_iff]
class IsProper extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f : Prop where
lemma isProper_eq : @IsProper =
    (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType := by
  ext X Y f
  rw [isProper_iff, ← and_assoc]
  rfl
namespace IsProper
instance : MorphismProperty.RespectsIso @IsProper := by
  rw [isProper_eq]
  infer_instance
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProper := by
  rw [isProper_eq]
  infer_instance
instance : MorphismProperty.IsMultiplicative @IsProper := by
  rw [isProper_eq]
  infer_instance
instance (priority := 900) [IsClosedImmersion f] : IsProper f where
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProper := by
  rw [isProper_eq]
  infer_instance
instance : IsLocalAtTarget @IsProper := by
  rw [isProper_eq]
  infer_instance
end IsProper
end AlgebraicGeometry