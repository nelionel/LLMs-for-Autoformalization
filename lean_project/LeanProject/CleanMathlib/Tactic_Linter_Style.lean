import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
open Lean Elab Command
namespace Mathlib.Linter
register_option linter.style.setOption : Bool := {
  defValue := false
  descr := "enable the `setOption` linter"
}
namespace Style.setOption
def parse_set_option : Syntax → Option Name
  | `(command|set_option $name:ident $_val) => some name.getId
  | `(set_option $name:ident $_val in $_x) => some name.getId
  | `(tactic|set_option $name:ident $_val in $_x) => some name.getId
  | _ => none
def is_set_option : Syntax → Bool :=
  fun stx ↦ parse_set_option stx matches some _name
def setOptionLinter : Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.style.setOption (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? is_set_option then
      if let some name := parse_set_option head then
        let forbidden := [`debug, `pp, `profiler, `trace]
        if forbidden.contains name.getRoot then
          Linter.logLint linter.style.setOption head
            m!"Setting options starting with '{"', '".intercalate (forbidden.map (·.toString))}' \
               is only intended for development and not for final code. \
               If you intend to submit this contribution to the Mathlib project, \
               please remove 'set_option {name}'."
initialize addLinter setOptionLinter
end Style.setOption
open Lean Elab Command
register_option linter.style.missingEnd : Bool := {
  defValue := false
  descr := "enable the missing end linter"
}
namespace Style.missingEnd
@[inherit_doc Mathlib.Linter.linter.style.missingEnd]
def missingEndLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless stx.isOfKind ``Lean.Parser.Command.eoi do return
    if Linter.getLinterValue linter.style.missingEnd (← getOptions) &&
        !(← MonadState.get).messages.hasErrors then
      let sc ← getScopes
      if sc.length == 1 then return
      let ends := sc.dropLast.map fun s ↦ (s.header, s.isNoncomputable)
      let ends := if ends.getLast!.2 then ends.dropLast else ends
      if !ends.isEmpty then
        let ending := (ends.map Prod.fst).foldl (init := "") fun a b ↦
          a ++ s!"\n\nend{if b == "" then "" else " "}{b}"
        Linter.logLint linter.style.missingEnd stx
         m!"unclosed sections or namespaces; expected: '{ending}'"
initialize addLinter missingEndLinter
end Style.missingEnd
register_option linter.style.cdot : Bool := {
  defValue := false
  descr := "enable the `cdot` linter"
}
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false
partial
def findCDot : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findCDot).flatten
    match kind with
      | ``Lean.Parser.Term.cdot | ``cdotTk => dargs.push stx
      | _ =>  dargs
  |_ => #[]
def unwanted_cdot (stx : Syntax) : Array Syntax :=
  (findCDot stx).filter (!isCDot? ·)
namespace Style
@[inherit_doc linter.style.cdot]
def cdotLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.style.cdot (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in unwanted_cdot stx do
      Linter.logLint linter.style.cdot s
        m!"Please, use '·' (typed as `\\.`) instead of '{s}' as 'cdot'."
    for cdot in Mathlib.Linter.findCDot stx do
      match cdot.find? (·.isOfKind `token.«· ») with
      | some (.node _ _ #[.atom (.original _ _ afterCDot _) _]) =>
        if (afterCDot.takeWhile (·.isWhitespace)).contains '\n' then
          logWarningAt cdot <| .tagged linter.style.cdot.name
            m!"This central dot `·` is isolated; please merge it with the next line."
      | _ => return
initialize addLinter cdotLinter
end Style
register_option linter.style.dollarSyntax : Bool := {
  defValue := false
  descr := "enable the `dollarSyntax` linter"
}
namespace Style.dollarSyntax
partial
def findDollarSyntax : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findDollarSyntax).flatten
    match kind with
      | ``«term_$__» => dargs.push stx
      | _ => dargs
  |_ => #[]
@[inherit_doc linter.style.dollarSyntax]
def dollarSyntaxLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.style.dollarSyntax (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in findDollarSyntax stx do
      Linter.logLint linter.style.dollarSyntax s
        m!"Please use '<|' instead of '$' for the pipe operator."
initialize addLinter dollarSyntaxLinter
end Style.dollarSyntax
register_option linter.style.lambdaSyntax : Bool := {
  defValue := false
  descr := "enable the `lambdaSyntax` linter"
}
namespace Style.lambdaSyntax
partial
def findLambdaSyntax : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findLambdaSyntax).flatten
    match kind with
      | ``Parser.Term.fun => dargs.push stx
      | _ =>  dargs
  |_ => #[]
@[inherit_doc linter.style.lambdaSyntax]
def lambdaSyntaxLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.style.lambdaSyntax (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in findLambdaSyntax stx do
      if let .atom _ "λ" := s[0] then
        Linter.logLint linter.style.lambdaSyntax s[0] m!"\
        Please use 'fun' and not 'λ' to define anonymous functions.\n\
        The 'λ' syntax is deprecated in mathlib4."
initialize addLinter lambdaSyntaxLinter
end Style.lambdaSyntax
register_option linter.style.longFile : Nat := {
  defValue := 0
  descr := "enable the longFile linter"
}
register_option linter.style.longFileDefValue : Nat := {
  defValue := 1500
  descr := "a soft upper bound on the number of lines of each file"
}
namespace Style.longFile
@[inherit_doc Mathlib.Linter.linter.style.longFile]
def longFileLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let linterBound := linter.style.longFile.get (← getOptions)
  if linterBound == 0 then
    return
  let defValue := linter.style.longFileDefValue.get (← getOptions)
  let smallOption := match stx with
      | `(set_option linter.style.longFile $x) => TSyntax.getNat ⟨x.raw⟩ ≤ defValue
      | _ => false
  if smallOption then
    logWarningAt stx <| .tagged linter.style.longFile.name
      m!"The default value of the `longFile` linter is {defValue}.\n\
        The current value of {linterBound} does not exceed the allowed bound.\n\
        Please, remove the `set_option linter.style.longFile {linterBound}`."
  else
  unless Parser.isTerminalCommand stx do return
  if (← getMainModule) == `Mathlib then return
  if let some init := stx.getTailPos? then
    let lastLine := ((← getFileMap).toPosition init).line
    if lastLine ≤ defValue && defValue < linterBound then
      logWarningAt stx <| .tagged linter.style.longFile.name
        m!"The default value of the `longFile` linter is {defValue}.\n\
          This file is {lastLine} lines long which does not exceed the allowed bound.\n\
          Please, remove the `set_option linter.style.longFile {linterBound}`."
    else
    let candidate := (lastLine / 100) * 100 + 200
    let candidate := max candidate defValue
    if defValue ≤ linterBound && linterBound < lastLine then
      logWarningAt stx <| .tagged linter.style.longFile.name
        m!"This file is {lastLine} lines long, but the limit is {linterBound}.\n\n\
          You can extend the allowed length of the file using \
          `set_option linter.style.longFile {candidate}`.\n\
          You can completely disable this linter by setting the length limit to `0`."
    else
    if linterBound == candidate || linterBound + 100 == candidate then return
    else
      logWarningAt stx <| .tagged linter.style.longFile.name
        m!"This file is {lastLine} lines long. \
          The current limit is {linterBound}, but it is expected to be {candidate}:\n\
          `set_option linter.style.longFile {candidate}`."
initialize addLinter longFileLinter
end Style.longFile
register_option linter.style.longLine : Bool := {
  defValue := false
  descr := "enable the longLine linter"
}
namespace Style.longLine
@[inherit_doc Mathlib.Linter.linter.style.longLine]
def longLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.style.longLine (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if stx.isOfKind ``Lean.guardMsgsCmd then
      return
    let stx := ← do
      if stx.isOfKind ``Lean.Parser.Command.eoi then
        let fileMap ← getFileMap
        let (impMods, _) ← Parser.parseHeader
          { input := fileMap.source, fileName := ← getFileName, fileMap := fileMap }
        return impMods
      else return stx
    let sstr := stx.getSubstring?
    let fm ← getFileMap
    let longLines := ((sstr.getD default).splitOn "\n").filter fun line ↦
      (100 < (fm.toPosition line.stopPos).column)
    for line in longLines do
      if (line.splitOn "http").length ≤ 1 then
        let stringMsg := if line.contains '"' then
          "\nYou can use \"string gaps\" to format long strings: within a string quotation, \
          using a '\\' at the end of a line allows you to continue the string on the following \
          line, removing all intervening whitespace."
        else ""
        Linter.logLint linter.style.longLine (.ofRange ⟨line.startPos, line.stopPos⟩)
          m!"This line exceeds the 100 character limit, please shorten it!{stringMsg}"
initialize addLinter longLineLinter
end Style.longLine
end Mathlib.Linter