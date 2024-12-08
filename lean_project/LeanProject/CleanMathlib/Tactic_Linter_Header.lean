import Lean.Elab.Command
import Lean.Elab.ParseImportsFast
import statements*
module doc-string*
remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.
The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.
## Implementation
The strategy used by the linter is as follows.
The linter computes the end position of the first module doc-string of the file,
resorting to the end of the file, if there is no module doc-string.
Next, the linter tries to parse the file up to the position determined above.
If the parsing is successful, the linter checks the resulting `Syntax` and behaves accordingly.
If the parsing is not successful, this already means there is some "problematic" command
after the imports. In particular, there is a command that is not a module doc-string
immediately following the last import: the file should be flagged by the linter.
Hence, the linter then falls back to parsing the header of the file, adding a spurious `section`
after it.
This makes it possible for the linter to check the entire header of the file, emit warnings that
could arise from this part and also flag that the file should contain a module doc-string after
the `import` statements.
-/
open Lean Elab Command
namespace Mathlib.Linter
def firstNonImport? : Syntax → Option Syntax
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] => args[0]?
  | _=> some .missing  
partial
def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  if s.isOfKind ``Lean.Parser.Module.import then
    rest.push (s.getArgs.getD 2 default)
  else
    rest
def parseUpToHere (pos : String.Pos) (post : String := "") : CommandElabM Syntax := do
  let upToHere : Substring := { str := (← getFileMap).source, startPos := ⟨0⟩, stopPos := pos }
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)
def toSyntax (s pattern : String) (offset : String.Pos := 0) : Syntax :=
  let beg := ((s.splitOn pattern).getD 0 "").endPos + offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).endPos + offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern
def authorsLineChecks (line : String) (offset : String.Pos) : Array (Syntax × String) :=
  Id.run do
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.push
      (toSyntax line (line.take "Authors: ".length) offset,
       s!"The authors line should begin with 'Authors: '")
  if (line.splitOn "  ").length != 1 then
    stxs := stxs.push (toSyntax line "  " offset, s!"Double spaces are not allowed.")
  if (line.splitOn " and ").length != 1 then
    stxs := stxs.push (toSyntax line " and " offset, s!"Please, do not use 'and'; use ',' instead.")
  if line.back == '.' then
    stxs := stxs.push
      (toSyntax line "." offset,
       s!"Please, do not end the authors' line with a period.")
  return stxs
")` pair, each on its own line;
* the first line is begins with `Copyright (c) 20` and ends with `. All rights reserved.`;
* the second line is `Released under Apache 2.0 license as described in the file LICENSE.`;
* the remainder of the string begins with `Authors: `, does not end with `.` and
  contains no ` and ` nor a double space, except possibly after a line break.
-/
def copyrightHeaderChecks (copyright : String) : Array (Syntax × String) := Id.run do
  let preprocessCopyright := (copyright.replace ",\n  " ", ").replace ",\n" ","
  let pieces := preprocessCopyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdText (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut output := #[]
  if (pieces.getD 1 "\n").take 1 != "\n" then
    output := output.push (toSyntax copyright "-/", s!"{stdText "-/"}")
  let lines := copyright.splitOn "\n"
  let closeComment := lines.getLastD ""
  match lines with
  | openComment :: copyrightAuthor :: license :: authorsLines =>
    match openComment, closeComment with
    | "" => output := output
    | ""}")
    | _, _       =>
      output := output.push (toSyntax copyright openComment, s!"{stdText ("/".push '-')}")
    let copStart := "Copyright (c) 20"
    let copStop := ". All rights reserved."
    if !copyrightAuthor.startsWith copStart then
      output := output.push
        (toSyntax copyright (copyrightAuthor.take copStart.length),
         s!"Copyright line should start with 'Copyright (c) YYYY'")
    if !copyrightAuthor.endsWith copStop then
      output := output.push
        (toSyntax copyright (copyrightAuthor.takeRight copStop.length),
         s!"Copyright line should end with '. All rights reserved.'")
    let authorsLines := authorsLines.dropLast
    if authorsLines.length == 0 then
      output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
    else
    let authorsLine := "\n".intercalate authorsLines
    let authorsStart := (("\n".intercalate [openComment, copyrightAuthor, license, ""])).endPos
    if authorsLines.length > 1 && !authorsLines.dropLast.all (·.endsWith ",") then
      output := output.push ((toSyntax copyright authorsLine),
        "If an authors line spans multiple lines, \
        each line but the last must end with a trailing comma")
    output := output.append (authorsLineChecks authorsLine authorsStart)
    let expectedLicense := "Released under Apache 2.0 license as described in the file LICENSE."
    if license != expectedLicense then
      output := output.push (toSyntax copyright license,
        s!"Second copyright line should be \"{expectedLicense}\"")
  | _ =>
    output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
  return output
def isInMathlib (modName : Name) : IO Bool := do
  let mlPath := ("Mathlib" : System.FilePath).addExtension "lean"
  if ← mlPath.pathExists then
    let ml ← parseImports' (← IO.FS.readFile mlPath) ""
    return (ml.map (·.module == modName)).any (·)
  else return false
initialize inMathlibRef : IO.Ref (Option Bool) ← IO.mkRef none
import statements*
module doc-string*
remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.
The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.
-/
register_option linter.style.header : Bool := {
  defValue := false
  descr := "enable the header style linter"
}
namespace Style.header
def broadImportsCheck (imports : Array Syntax) (mainModule : Name) : CommandElabM Unit := do
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic =>
      Linter.logLint linter.style.header i "Files in mathlib cannot import the whole tactic folder."
    | `Mathlib.Tactic.Replace =>
      if mainModule != `Mathlib.Tactic then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Replace' defines a deprecated form of the 'replace' tactic; \
          please do not use it in mathlib."
    | `Mathlib.Tactic.Have =>
      if ![`Mathlib.Tactic, `Mathlib.Tactic.Replace].contains mainModule then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Have' defines a deprecated form of the 'have' tactic; \
          please do not use it in mathlib."
    | modName =>
      if modName.getRoot == `Lake then
      Linter.logLint linter.style.header i
        "In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter \
        (see e.g. https://github.com/leanprover-community/mathlib4/pull/13779). Please consider carefully if this import is useful and \
        make sure to benchmark it. If this is fine, feel free to silence this linter."
      else if (`Mathlib.Deprecated).isPrefixOf modName &&
          !(`Mathlib.Deprecated).isPrefixOf mainModule then
        Linter.logLint linter.style.header i
          "Files in the `Deprecated` directory are not supposed to be imported."
def duplicateImportsCheck (imports : Array Syntax)  : CommandElabM Unit := do
  let mut importsSoFar := #[]
  for i in imports do
    if importsSoFar.contains i then
      Linter.logLint linter.style.header i m!"Duplicate imports: '{i}' already imported"
    else importsSoFar := importsSoFar.push i
@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let mainModule ← getMainModule
  let inMathlib? := ← match ← inMathlibRef.get with
    | some d => return d
    | none => do
      let val ← isInMathlib mainModule
      inMathlibRef.set (some val)
      return val
  unless inMathlib? || mainModule == `MathlibTest.Header do return
  unless Linter.getLinterValue linter.style.header (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if mainModule == `Mathlib then return
  let fm ← getFileMap
  let md := (getMainModuleDoc (← getEnv)).toArray
  let firstDocModPos := match md[0]? with
                          | none     => fm.positions.back!
                          | some doc => fm.ofPosition doc.declarationRange.endPos
  unless stx.getTailPos?.getD default ≤ firstDocModPos do
    return
  let upToStx ← parseUpToHere firstDocModPos <|> (do
    let fil ← getFileName
    let (stx, _) ← Parser.parseHeader { input := fm.source, fileName := fil, fileMap := fm }
    parseUpToHere (stx.getTailPos?.getD default) "\nsection")
  let importIds := getImportIds upToStx
  broadImportsCheck importIds mainModule
  duplicateImportsCheck importIds
  let afterImports := firstNonImport? upToStx
  if afterImports.isNone then return
  let copyright := match upToStx.getHeadInfo with
    | .original lead .. => lead.toString
    | _ => ""
  if mainModule != `Mathlib.Init then
    for (stx, m) in copyrightHeaderChecks copyright do
      Linter.logLint linter.style.header stx m!"* '{stx.getAtomVal}':\n{m}\n"
  match afterImports with
    | none => return
    | some (.node _ ``Lean.Parser.Command.moduleDoc _) => return
    | some rest =>
    Linter.logLint linter.style.header rest
      m!"The module doc-string for a file should be the first command after the imports.\n\
       Please, add a module doc-string before `{stx}`."
initialize addLinter headerLinter
end Style.header
end Mathlib.Linter