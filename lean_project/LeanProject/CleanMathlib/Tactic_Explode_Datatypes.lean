import Mathlib.Init
import Lean.Util.Trace
open Lean
namespace Mathlib.Explode
initialize registerTraceClass `explode
inductive Status where
  | sintro : Status
  | intro  : Status
  | cintro : Status
  | lam    : Status
  | reg    : Status
  deriving Inhabited
structure Entry where
  type     : MessageData
  line     : Option Nat := none
  depth    : Nat
  status   : Status
  thm      : MessageData
  deps     : List (Option Nat)
  useAsDep : Bool
def Entry.line! (entry : Entry) : Nat := entry.line.get!
structure Entries : Type where
  s : ExprMap Entry
  l : List Entry
  deriving Inhabited
def Entries.find? (es : Entries) (e : Expr) : Option Entry :=
  es.s[e]?
def Entries.size (es : Entries) : Nat :=
  es.s.size
def Entries.add (entries : Entries) (expr : Expr) (entry : Entry) : Entry × Entries :=
  if let some entry' := entries.find? expr then
    (entry', entries)
  else
    let entry := { entry with line := entries.size }
    (entry, ⟨entries.s.insert expr entry, entry :: entries.l⟩)
def Entries.addSynonym (entries : Entries) (expr : Expr) (entry : Entry) : Entries :=
  ⟨entries.s.insert expr entry, entries.l⟩
end Explode
end Mathlib