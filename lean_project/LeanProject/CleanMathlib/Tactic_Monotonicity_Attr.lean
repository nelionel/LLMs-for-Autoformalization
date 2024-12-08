import Mathlib.Init
import Lean.LabelAttribute
namespace Mathlib.Tactic.Monotonicity
syntax mono.side := &"left" <|> &"right" <|> &"both"
namespace Attr
syntax (name := mono) "mono" (ppSpace mono.side)? : attr
open Lean in
@[inherit_doc mono]
initialize ext : LabelExtension ← (
  let descr := "A lemma stating the monotonicity of some function, with respect to appropriate
relations on its domain and range, and possibly with side conditions."
  let mono := `mono
  registerLabelAttr mono descr mono)
end Attr
end Monotonicity
end Mathlib.Tactic