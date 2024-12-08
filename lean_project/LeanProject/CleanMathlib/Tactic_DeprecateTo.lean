import Lean.Meta.Tactic.TryThis
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Lemma
namespace Mathlib.Tactic.DeprecateTo
open Lean Elab Term Command
def mkDeprecationStx (id : TSyntax `ident) (n : Name) (dat : Option String := none) :
    CommandElabM (TSyntax `command) := do
  let dat := ← match dat with
                | none => IO.Process.run { cmd := "date", args := #["-I"] }
                | some s => return s
  let nd := mkNode `str #[mkAtom ("\"" ++ dat.trimRight ++ "\"")]
  `(command| @[deprecated (since := $nd)] alias $(mkIdent n) := $id)
def newNames (old new : Environment) : Array Name := Id.run do
  let mut diffs := #[]
  for (c, _) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push c
  pure <| diffs.qsort (·.toString < ·.toString)
variable (newName : TSyntax `ident) in
def renameTheorem : TSyntax `command → TSyntax `Lean.Parser.Command.declId × TSyntax `command
  | `(command| $dm:declModifiers theorem $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers theorem $newName:declId $d:declSig $v:declVal))
  | `(command| $dm:declModifiers lemma $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers lemma $newName:declId $d:declSig $v:declVal))
  | a => (default, a)
open Meta.Tactic.TryThis in
elab tk:"deprecate" "to" id:ident* dat:(ppSpace str ppSpace)? ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    let allNew := newNames oldEnv newEnv
    let skip ← allNew.filterM (·.isBlackListed)
    let mut news := allNew.filter (! · ∈ skip)
    let mut warn := #[]
    if id.size < news.size then
      warn := warn.push s!"Un-deprecated declarations: {news.toList.drop id.size}"
    if news.size < id.size then
      for i in id.toList.drop news.size do logErrorAt i ""
      warn := warn.push s!"Unused names: {id.toList.drop news.size}"
    let (oldId, newCmd) := renameTheorem id[0]! cmd
    let oldNames := ← resolveGlobalName (oldId.raw.getArg 0).getId.eraseMacroScopes
    let fil := news.filter fun n => n.toString.endsWith oldNames[0]!.1.toString
    if fil.size != 1 && oldId != default then
      logError m!"Expected to find one declaration called {oldNames[0]!.1}, found {fil.size}"
    if oldId != default then
      news := #[fil[0]!] ++ (news.erase fil[0]!)
    let pairs := id.zip news
    let msg := s!"* Pairings:\n{pairs.map fun (l, r) => (l.getId, r)}" ++
      if skip.size != 0 then s!"\n\n* Ignoring: {skip}" else ""
    let dat := if dat.isSome then some dat.get!.getString else none
    let stxs ← pairs.mapM fun (id, n) => mkDeprecationStx id n dat
    if newCmd == cmd then
      logWarningAt cmd m!"New declaration uses the old name {oldId.raw.getArg 0}!"
    let stxs := #[newCmd] ++ stxs
    if warn != #[] then
      logWarningAt tk m!"{warn.foldl (· ++ "\n" ++ ·) "Warnings:\n"}"
    liftTermElabM do
      let prettyStxs ← stxs.mapM (SuggestionText.prettyExtra <|.tsyntax ·)
      let toMessageData := (prettyStxs.toList.drop 1).foldl
        (fun x y => x ++ "\n\n" ++ y) prettyStxs[0]!
      addSuggestion (header := msg ++ "\n\nTry this:\n") (← getRef)
        toMessageData
end Mathlib.Tactic.DeprecateTo