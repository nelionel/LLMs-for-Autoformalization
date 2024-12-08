import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Monoid.Submonoid
assert_not_exists Finset
@[to_additive]
instance SubmonoidClass.instMulArchimedean {M S : Type*} [SetLike S M] [OrderedCommMonoid M]
    [SubmonoidClass S M] [MulArchimedean M] (H : S) : MulArchimedean H := by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one, SubmonoidClass.mk_pow, Subtype.mk_le_mk]
  exact MulArchimedean.arch x.val