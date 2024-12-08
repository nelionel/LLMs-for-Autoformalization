import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
namespace CategoryTheory
namespace Idempotents
variable {C : Type*} [Category C] [IsIdempotentComplete C]
instance : IsIdempotentComplete (SimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _
instance : IsIdempotentComplete (CosimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _
end Idempotents
end CategoryTheory