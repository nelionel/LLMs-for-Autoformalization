import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation
open System
namespace Mathlib.Linter.TextBased
inductive BroadImports
  | TacticFolder
  | Lake
deriving BEq
inductive StyleError where
  | adaptationNote
  | windowsLineEnding
  | trailingWhitespace
deriving BEq
inductive ErrorFormat
  | humanReadable : ErrorFormat
  | exceptionsFile : ErrorFormat
  | github : ErrorFormat
  deriving BEq
def StyleError.errorMessage (err : StyleError) : String := match err with
  | StyleError.adaptationNote =>
    "Found the string \"Adaptation note:\", please use the #adaptation_note command instead"
  | windowsLineEnding => "This line ends with a windows line ending (\r\n): please use Unix line\
    endings (\n) instead"
  | trailingWhitespace => "This line ends with some whitespace: please remove this"
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.windowsLineEnding => "ERR_WIN"
  | StyleError.trailingWhitespace => "ERR_TWS"
structure ErrorContext where
  error : StyleError
  lineNumber : ℕ
  path : FilePath
inductive ComparisonResult
  | Different
  | Comparable
  deriving BEq
def compare (existing new : ErrorContext) : ComparisonResult :=
  if existing.path.components != new.path.components then ComparisonResult.Different
  else
    if existing.error == new.error then ComparisonResult.Comparable else ComparisonResult.Different
def ErrorContext.find?_comparable (e : ErrorContext) (exceptions : Array ErrorContext) :
    Option ErrorContext :=
  (exceptions).find? (fun new ↦ compare e new == ComparisonResult.Comparable)
def outputMessage (errctx : ErrorContext) (style : ErrorFormat) : String :=
  let errorMessage := errctx.error.errorMessage
  match style with
  | ErrorFormat.github =>
    let path := errctx.path
    let nr := errctx.lineNumber
    let code := errctx.error.errorCode
    s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errorMessage}"
  | ErrorFormat.exceptionsFile =>
    s!"{errctx.path} : line {errctx.lineNumber} : {errctx.error.errorCode} : {errorMessage}"
  | ErrorFormat.humanReadable =>
    s!"error: {errctx.path}:{errctx.lineNumber}: {errorMessage}"
def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (· == ' ')
  match parts with
    | filename :: ":" :: "line" :: lineNumber :: ":" :: errorCode :: ":" :: _errorMessage =>
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      let err : Option StyleError := match errorCode with
        | "ERR_ADN" => some (StyleError.adaptationNote)
        | "ERR_TWS" => some (StyleError.trailingWhitespace)
        | "ERR_WIN" => some (StyleError.windowsLineEnding)
        | _ => none
      match String.toNat? lineNumber with
      | some n => err.map fun e ↦ (ErrorContext.mk e n path)
      | _ => none
    | _ => none
def parseStyleExceptions (lines : Array String) : Array ErrorContext := Id.run do
  Array.filterMap (parse?_errorContext ·) (lines.filter (fun line ↦ !line.startsWith "
def formatErrors (errors : Array ErrorContext) (style : ErrorFormat) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e style)
abbrev TextbasedLinter := Array String → Array (StyleError × ℕ) × (Option (Array String))
section
def adaptationNoteLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  for (line, idx) in lines.zipWithIndex do
    if line.containsSubstr "daptation note" then
      errors := errors.push (StyleError.adaptationNote, idx + 1)
  return (errors, none)
def trailingWhitespaceLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  let mut fixedLines := lines
  for (line, idx) in lines.zipWithIndex do
    if line.back == ' ' then
      errors := errors.push (StyleError.trailingWhitespace, idx + 1)
      fixedLines := fixedLines.set! idx line.trimRight
  return (errors, if errors.size > 0 then some fixedLines else none)
def isImportsOnlyFile (lines : Array String) : Bool :=
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "
end
def allLinters : Array TextbasedLinter := #[
    adaptationNoteLinter, trailingWhitespaceLinter
  ]
def lintFile (path : FilePath) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext × Option (Array String)) := do
  let mut errors := #[]
  let mut changes_made := false
  let contents ← IO.FS.readFile path
  let replaced := contents.crlfToLf
  if replaced != contents then
    changes_made := true
    errors := errors.push (ErrorContext.mk StyleError.windowsLineEnding 1 path)
  let lines := (replaced.splitOn "\n").toArray
  if isImportsOnlyFile lines then
    return (errors, if changes_made then some lines else none)
  let mut allOutput := #[]
  let mut changed := lines
  for lint in allLinters do
    let (err, changes) := lint changed
    allOutput := allOutput.append (Array.map (fun (e, n) ↦ #[(ErrorContext.mk e n path)]) err)
    if let some c := changes then
      changed := c
      changes_made := true
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return (errors, if changes_made then some changed else none)
def lintModules (moduleNames : Array Lean.Name) (style : ErrorFormat) (fix : Bool) : IO UInt32 := do
  let nolints ← IO.FS.lines ("scripts" / "nolints-style.txt")
  let styleExceptions := parseStyleExceptions nolints
  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    let path := mkFilePath (module.components.map toString)|>.addExtension "lean"
    let (errors, changed) := ← lintFile path styleExceptions
    if let some c := changed then
      if fix then
        let _ := ← IO.FS.writeFile path ("\n".intercalate c.toList)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1
  let args := if fix then #["
  let output ← IO.Process.output { cmd := "./scripts/print-style-errors.sh", args := args }
  if output.exitCode != 0 then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprintln s!"error: `print-style-error.sh` exited with code {output.exitCode}"
    IO.eprint output.stderr
  else if output.stdout != "" then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprint output.stdout
  formatErrors allUnexpectedErrors style
  if allUnexpectedErrors.size > 0 then
    IO.eprintln s!"error: found {allUnexpectedErrors.size} new style error(s)"
  return numberErrorFiles
end Mathlib.Linter.TextBased