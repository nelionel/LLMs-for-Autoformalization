import Mathlib.Init
import Lean.Message
open Lean Std MessageData
instance {α β : Type} [ToMessageData α] [ToMessageData β] : ToMessageData (α × β) :=
  ⟨fun x => paren <| toMessageData x.1 ++ ofFormat "," ++ Format.line ++ toMessageData x.2⟩