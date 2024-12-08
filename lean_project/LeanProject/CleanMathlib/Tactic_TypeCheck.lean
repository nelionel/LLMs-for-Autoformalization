import Mathlib.Init
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars
open Lean Elab Meta
elab tk:"type_check " e:term : tactic => do
  Tactic.withMainContext do
    let e ← Term.elabTermAndSynthesize e none
    check e
    let type ← inferType e
    Lean.logInfoAt tk m!"{← Lean.instantiateMVars type}"