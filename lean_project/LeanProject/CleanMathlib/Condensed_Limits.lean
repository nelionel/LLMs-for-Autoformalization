import Mathlib.Condensed.Module
universe u
open CategoryTheory Limits
instance : HasLimits CondensedSet.{u} := by
  change HasLimits (Sheaf _ _)
  infer_instance
instance : HasLimitsOfSize.{u, u + 1} CondensedSet.{u} :=
  hasLimitsOfSizeShrink.{u, u+1, u+1, u} _
variable (R : Type (u+1)) [Ring R]
instance : HasLimits (CondensedMod.{u} R) := by
  change HasLimits (Sheaf _ _)
  infer_instance
instance : HasLimitsOfSize.{u, u + 1} (CondensedMod.{u} R) :=
  hasLimitsOfSizeShrink.{u, u+1, u+1, u} _