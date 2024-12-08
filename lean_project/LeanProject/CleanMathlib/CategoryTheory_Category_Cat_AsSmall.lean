import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.ULift
universe w v u
namespace CategoryTheory
namespace Cat
@[simps]
def asSmallFunctor : Cat.{v, u} ⥤ Cat.{max w v u, max w v u} where
  obj C := .of <| AsSmall C
  map F := AsSmall.down ⋙ F ⋙ AsSmall.up
end Cat
end CategoryTheory