import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.ToAdditive
universe u
@[to_additive]
instance SemigroupPEmpty : Semigroup PEmpty.{u + 1} where
  mul x _ := by cases x
  mul_assoc x y z := by cases x