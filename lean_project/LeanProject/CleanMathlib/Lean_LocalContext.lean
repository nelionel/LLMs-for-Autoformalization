import Mathlib.Init
import Lean.LocalContext
namespace Lean.LocalContext
universe u v
variable {m : Type u → Type v} [Monad m] [Alternative m]
variable {β : Type u}
@[specialize] def firstDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b
@[specialize] def lastDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b
end Lean.LocalContext