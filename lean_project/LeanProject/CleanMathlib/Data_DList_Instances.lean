import Batteries.Data.DList.Lemmas
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances
open Function Equiv
namespace Batteries
variable (α : Type*)
def DList.listEquivDList : List α ≃ DList α where
  toFun := DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _
instance : Traversable DList :=
  Equiv.traversable DList.listEquivDList
instance : LawfulTraversable DList :=
  Equiv.isLawfulTraversable DList.listEquivDList
instance {α} : Inhabited (DList α) :=
  ⟨DList.empty⟩
end Batteries