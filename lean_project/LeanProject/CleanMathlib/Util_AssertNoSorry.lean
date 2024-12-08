import Mathlib.Init
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Meta Elab Command
elab "assert_no_sorry " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``sorryAx
  then throwError "{n} contains sorry"