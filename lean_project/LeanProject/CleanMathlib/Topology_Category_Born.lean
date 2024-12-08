import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.Bornology.Hom
universe u
open CategoryTheory
def Born :=
  Bundled Bornology
namespace Born
instance : CoeSort Born Type* :=
  Bundled.coeSort
instance (X : Born) : Bornology X :=
  X.str
def of (α : Type*) [Bornology α] : Born :=
  Bundled.of α
instance : Inhabited Born :=
  ⟨of PUnit⟩
instance : BundledHom @LocallyBoundedMap where
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext _ _ := DFunLike.coe_injective
instance : LargeCategory.{u} Born :=
  BundledHom.category LocallyBoundedMap
instance : ConcreteCategory Born :=
  BundledHom.concreteCategory LocallyBoundedMap
end Born