import Lean.Elab.Command
import Mathlib.Init
namespace Mathlib.GuardExceptions
open Lean Parser Elab Command
def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.input.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)
#guard_msgs in #parse Mathlib.Stacks.stacksTagFn => "A05"
```
-/
syntax (name := parseCmd) "#parse " ident " => " str : command
@[inherit_doc parseCmd]
elab_rules : command
  | `(command| #parse $parserFnId => $str) => do
    elabCommand <| ← `(command|
      run_cmd do
        let exc ← Lean.ofExcept <| captureException (← getEnv) $parserFnId $str
        logInfo $str)
end Mathlib.GuardExceptions