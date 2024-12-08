import Mathlib.Init
import Batteries.Data.MLList.Basic
import Batteries.Data.HashMap.Basic
set_option linter.deprecated false
open Batteries
namespace MLList
variable {α β : Type} {m : Type → Type} [Monad m] [BEq β] [Hashable β]
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def dedupBy (L : MLList m α) (f : α → m β) : MLList m α :=
  ((L.liftM : MLList (StateT (HashMap β Unit) m) α) >>= fun a => do
      let b ← f a
      guard !(← get).contains b
      modify fun s => s.insert b ()
      pure a)
  |>.runState' ∅
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def dedup (L : MLList m β) : MLList m β := L.dedupBy pure
end MLList