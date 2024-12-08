import Batteries.Data.RBMap.Basic
import Mathlib.Data.Tree.Basic
namespace Tree
universe u
variable {α : Type u}
open Batteries (RBNode)
def ofRBNode : RBNode α → Tree α
  | RBNode.nil => nil
  | RBNode.node _color l key r => node key (ofRBNode l) (ofRBNode r)
end Tree