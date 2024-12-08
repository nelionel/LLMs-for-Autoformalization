import Mathlib.Init
import Lean.Elab.Tactic.Conv.Basic
import Lean.Elab.Command
namespace Mathlib.Tactic.Conv
open Lean Parser.Tactic Parser.Tactic.Conv Elab.Tactic Meta
syntax (name := convLHS) "conv_lhs" (" at " ident)? (" in " (occs)? term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_lhs $[at $id]? $[in $[$occs]? $pat]? => $seq) =>
    `(tactic| conv $[at $id]? $[in $[$occs]? $pat]? => lhs; ($seq:convSeq))
syntax (name := convRHS) "conv_rhs" (" at " ident)? (" in " (occs)? term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_rhs $[at $id]? $[in $[$occs]? $pat]? => $seq) =>
    `(tactic| conv $[at $id]? $[in $[$occs]? $pat]? => rhs; ($seq:convSeq))
macro "run_conv" e:doSeq : conv => `(conv| tactic' => run_tac $e)
macro "conv" " in " occs?:(occs)? p:term " => " code:convSeq : conv =>
  `(conv| conv => pattern $[$occs?]? $p; ($code:convSeq))
syntax (name := dischargeConv) "discharge" (" => " tacticSeq)? : conv
@[tactic dischargeConv] def elabDischargeConv : Tactic := fun
  | `(conv| discharge $[=> $tac]?) => do
    let g :: gs ← getGoals | throwNoGoalsToBeSolved
    let (theLhs, theRhs) ← Conv.getLhsRhsCore g
    let .true ← isProp theLhs | throwError "target is not a proposition"
    theRhs.mvarId!.assign (mkConst ``True)
    let m ← mkFreshExprMVar theLhs
    g.assign (← mkEqTrue m)
    if let some tac := tac then
      setGoals [m.mvarId!]
      evalTactic tac; done
      setGoals gs
    else
      setGoals (m.mvarId! :: gs)
  | _ => Elab.throwUnsupportedSyntax
macro "refine " e:term : conv => `(conv| tactic => refine $e)
open Elab Tactic
elab tk:"#conv " conv:conv " => " e:term : command =>
  Command.runTermElabM fun _ ↦ do
    let e ← Elab.Term.elabTermAndSynthesize e none
    let (rhs, g) ← Conv.mkConvGoalFor e
    _ ← Tactic.run g.mvarId! do
      evalTactic conv
      for mvarId in (← getGoals) do
        liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
      pruneSolvedGoals
      let e' ← instantiateMVars rhs
      logInfoAt tk e'
@[inherit_doc Parser.Tactic.withReducible]
macro (name := withReducible) tk:"with_reducible " s:convSeq : conv =>
  `(conv| tactic' => with_reducible%$tk conv' => $s)
macro tk:"#whnf " e:term : command => `(command| #conv%$tk whnf => $e)
macro tk:"#whnfR " e:term : command => `(command| #conv%$tk with_reducible whnf => $e)
syntax "#simp" (&" only")? (simpArgs)? " =>"? ppSpace term : command
macro_rules
  | `(#simp%$tk $[only%$o]? $[[$args,*]]? $[=>]? $e) =>
    `(#conv%$tk simp $[only%$o]? $[[$args,*]]? => $e)
end Mathlib.Tactic.Conv