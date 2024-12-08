import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Star.Basic
notation:25 M " →ₗ⋆[" R:25 "] " M₂:0 => LinearMap (starRingEnd R) M M₂
notation:50 M " ≃ₗ⋆[" R "] " M₂ => LinearEquiv (starRingEnd R) M M₂