import Mathlib.Condensed.Light.Module
universe u
open CategoryTheory Limits
instance : HasLimitsOfSize.{u, u} LightCondSet.{u} := by
  change HasLimitsOfSize (Sheaf _ _)
  infer_instance
instance : HasFiniteLimits LightCondSet.{u} := hasFiniteLimits_of_hasLimitsOfSize _
variable (R : Type u) [Ring R]
instance : HasLimitsOfSize.{u, u} (LightCondMod.{u} R) := by
  change HasLimitsOfSize (Sheaf _ _)
  infer_instance
instance : HasFiniteLimits (LightCondMod.{u} R) := hasFiniteLimits_of_hasLimitsOfSize _