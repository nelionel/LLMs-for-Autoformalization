import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Embedding.Basic
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
variable {G : Type*}
section LeftOrRightCancelSemigroup
@[to_additive (attr := simps)
      "If left-addition by any element is cancellative, left-addition by `g` is an
        embedding."]
def mulLeftEmbedding [Mul G] [IsLeftCancelMul G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g
@[to_additive (attr := simps)
      "If right-addition by any element is cancellative, right-addition by `g` is an
        embedding."]
def mulRightEmbedding [Mul G] [IsRightCancelMul G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g
@[to_additive]
theorem mulLeftEmbedding_eq_mulRightEmbedding [CommSemigroup G] [IsCancelMul G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _
end LeftOrRightCancelSemigroup