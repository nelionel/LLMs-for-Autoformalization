import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.TryThis
syntax (name := change?) "change?" (ppSpace colGt term)? : tactic
open Lean Meta Elab.Tactic Meta.Tactic.TryThis in
elab_rules : tactic
| `(tactic|change?%$tk $[$sop:term]?) => withMainContext do
  let stx ← getRef
  let expr ← match sop with
    | none => getMainTarget
    | some sop => do
      let tgt ← getMainTarget
      let ex ← withRef sop <| elabTermEnsuringType sop (← inferType tgt)
      if !(← isDefEq ex tgt) then throwErrorAt sop "\
        The term{indentD ex}\n\
        is not defeq to the goal:{indentD tgt}"
      instantiateMVars ex
  let dstx ← delabToRefinableSyntax expr
  addSuggestion tk (← `(tactic| change $dstx)) (origSpan? := stx)