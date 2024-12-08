import Mathlib.Init
import Lean.Meta.Tactic.TryThis
import Batteries.Linter.UnreachableTactic
import Qq.Match
open Lean Elab Tactic
open Lean.Meta.Tactic.TryThis
namespace Mathlib.Tactic.Says
register_option says.verify : Bool :=
  { defValue := false
    group := "says"
    descr := "For every appearance of the `X says Y` combinator, \
      re-verify that running `X` produces `Try this: Y`." }
register_option says.no_verify_in_CI : Bool :=
  { defValue := false
    group := "says"
    descr := "Disable reverification, even if the `CI` environment variable is set." }
open Parser Tactic
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)
def evalTacticCapturingMessages (tac : TSyntax `tactic) (only : Message → Bool := fun _ => true) :
    TacticM (List Message) := do
  let mut msgs ← modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
  try
    evalTactic tac
    let (capture, leave) := (← getThe Core.State).messages.toList.partition only
    msgs := leave.foldl (·.add) msgs
    return capture
  catch e =>
    msgs := msgs ++ (← getThe Core.State).messages
    throw e
  finally
    modifyThe Core.State fun st => { st with messages := msgs }
def evalTacticCapturingInfo (tac : TSyntax `tactic) : TacticM (List Message) :=
  evalTacticCapturingMessages tac fun m => match m.severity with | .information => true | _ => false
def evalTacticCapturingTryThis (tac : TSyntax `tactic) : TacticM (TSyntax ``tacticSeq) := do
  let msg ← match ← evalTacticCapturingInfo tac with
  | [] => throwError m!"Tactic `{tac}` did not produce any messages."
  | [msg] => msg.toString
  | _ => throwError m!"Tactic `{tac}` produced multiple messages."
  let tryThis ← match msg.dropPrefix? "Try this:" with
  | none => throwError m!"Tactic output did not begin with 'Try this:': {msg}"
  | some S => pure S.toString.removeLeadingSpaces
  match parseAsTacticSeq (← getEnv) tryThis with
  | .ok stx => return stx
  | .error err => throwError m!"Failed to parse tactic output: {tryThis}\n{err}"
syntax (name := says) tactic " says" (colGt tacticSeq)? : tactic
elab_rules : tactic
  | `(tactic| $tac:tactic says%$tk $[$result:tacticSeq]?) => do
  let verify := says.verify.get (← getOptions) ||
    !says.no_verify_in_CI.get (← getOptions) && (← IO.getEnv "CI").isSome
  match result, verify with
  | some _, true
  | none, _ =>
    let stx ← evalTacticCapturingTryThis tac
    match result with
    | some r =>
        let stx' := (← Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos stx⟩).pretty
        let r' := (← Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos r⟩).pretty
        if stx' != r' then
          throwError m!"Tactic `{tac}` produced `{stx'}`,\nbut was expecting it to produce `{r'}`!"
            ++ m!"\n\nYou can reproduce this error locally using `set_option says.verify true`."
    | none =>
    addSuggestion tk (← `(tactic| $tac says $stx)) (origSpan? := (← `(tactic| $tac says)))
  | some result, false =>
    evalTactic result
initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind `Mathlib.Tactic.Says.says
end Says
end Mathlib.Tactic