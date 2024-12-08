import Mathlib.Init
import Lean.Elab.ElabRules
open Lean Elab
private def setOption {m : Type → Type} [Monad m] [MonadError m]
    (name val : Syntax) (opts : Options) : m Options := do
  let val ← match val with
    | Syntax.ident _ _ `true _  => pure <| DataValue.ofBool true
    | Syntax.ident _ _ `false _ => pure <| DataValue.ofBool false
    | _ => match val.isNatLit? with
      | some num => pure <| DataValue.ofNat num
      | none => match val.isStrLit? with
        | some str => pure <| DataValue.ofString str
        | none => throwError "unsupported option value {val}"
  pure <| opts.insert name.getId val
open Elab.Command in
elab "sudo " "set_option " n:ident ppSpace val:term : command => do
  let options ← setOption n val (← getOptions)
  modify fun s ↦ { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope ↦ { scope with opts := options }
open Elab.Term in
elab "sudo " "set_option " n:ident ppSpace val:term " in " body:term : term <= expectedType => do
  let options ← setOption n val (← getOptions)
  withTheReader Core.Context (fun ctx ↦
      { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    elabTerm body expectedType