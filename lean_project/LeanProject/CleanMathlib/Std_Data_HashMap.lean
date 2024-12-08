import Std.Data.HashMap.Basic
import Mathlib.Init
namespace Std.HashMap
variable {α β γ : Type _} [BEq α] [Hashable α]
def mapVal (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  m.fold (fun acc k v => acc.insert k (f k v)) HashMap.empty
end Std.HashMap