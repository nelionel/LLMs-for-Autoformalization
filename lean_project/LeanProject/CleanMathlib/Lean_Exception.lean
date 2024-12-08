import Mathlib.Init
import Lean.Exception
open Lean
def successIfFail {α : Type} {M : Type → Type} [MonadError M] [Monad M] (m : M α) :
    M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex
namespace Lean
namespace Exception
def isFailedToSynthesize (e : Exception) : IO Bool := do
  pure <| (← e.toMessageData.toString).startsWith "failed to synthesize"
end Exception
end Lean