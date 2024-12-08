import Mathlib.Logic.Small.Basic
import Mathlib.Data.Vector.Basic
universe u v
open Mathlib
instance smallVector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (Mathlib.Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).injective
instance smallList {α : Type v} [Small.{u} α] : Small.{u} (List α) := by
  let e : (Σn, Mathlib.Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective