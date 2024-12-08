import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.SingleObj
namespace CategoryTheory
variable {α : Type*} [Ring α]
instance : Preadditive (SingleObj α) where
  add_comp _ _ _ f f' g := mul_add g f f'
  comp_add _ _ _ f g g' := add_mul g g' f
end CategoryTheory