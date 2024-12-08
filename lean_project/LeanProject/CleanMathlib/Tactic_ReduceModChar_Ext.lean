import Mathlib.Init
import Lean.Meta.Tactic.Simp.Attr
open Lean Meta
initialize reduceModCharExt : SimpExtension ←
  registerSimpAttr `reduce_mod_char
    "lemmas for preprocessing and cleanup in the `reduce_mod_char` tactic"