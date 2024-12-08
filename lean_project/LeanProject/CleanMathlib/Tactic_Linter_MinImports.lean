import ImportGraph.Imports
import Mathlib.Tactic.MinImports
open Lean Elab Command
namespace Mathlib.Linter
structure ImportState where
  transClosure : Option (NameMap NameSet) := none
  minImports   : NameSet := {}
  importSize   : Nat := 0
  deriving Inhabited
initialize minImportsRef : IO.Ref ImportState ← IO.mkRef {}
elab "#reset_min_imports" : command => minImportsRef.set {}
register_option linter.minImports : Bool := {
  defValue := false
  descr := "enable the minImports linter"
}
register_option linter.minImports.increases : Bool := {
  defValue := true
  descr := "enable reporting increase-size change in the minImports linter"
}
namespace MinImports
open Mathlib.Command.MinImports
def importsBelow (tc : NameMap NameSet) (ms : NameSet) : NameSet :=
  ms.fold (·.append <| tc.findD · default) ms
@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.minImports (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.minImports) true)) then return
    let env ← getEnv
    if (← minImportsRef.get).transClosure.isNone then
      minImportsRef.modify ({· with transClosure := env.importGraph.transitiveClosure})
    let impState ← minImportsRef.get
    let (importsSoFar, oldCumulImps) := (impState.minImports, impState.importSize)
    if #[``Parser.Command.eoi, ``Lean.Parser.Command.exit].contains stx.getKind then
      let explicitImportsInFile : NameSet :=
        .fromArray ((env.imports.map (·.module)).erase `Init) Name.quickCmp
      let newImps := importsSoFar.diff explicitImportsInFile
      let currentlyUnneededImports := explicitImportsInFile.diff importsSoFar
      let fname ← getFileName
      let contents ← IO.FS.readFile fname
      let (impMods, _) ← Parser.parseHeader (Parser.mkInputContext contents fname)
      for i in currentlyUnneededImports do
        match impMods.find? (·.getId == i) with
          | some impPos => logWarningAt impPos m!"unneeded import '{i}'"
          | _ => dbg_trace f!"'{i}' not found"  
      if !newImps.isEmpty then
        let withImport := (newImps.toArray.qsort Name.lt).map (s!"import {·}")
        logWarningAt ((impMods.find? (·.isOfKind `import)).getD default)
          m!"
    let id ← getId stx
    let newImports := getIrredundantImports env (← getAllImports stx id)
    let tot := (newImports.append importsSoFar)
    let redundant := env.findRedundantImports tot.toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if currImpArray != #[] &&
       currImpArray ≠ importsSoFar.toArray.qsort Name.lt then
      let newCumulImps := 
        (importsBelow (impState.transClosure.getD env.importGraph.transitiveClosure) tot).size
      minImportsRef.modify ({· with minImports := currImports, importSize := newCumulImps})
      let new := currImpArray.filter (!importsSoFar.contains ·)
      let redundant := importsSoFar.toArray.filter (!currImports.contains ·)
      let byCount :=  if Linter.getLinterValue linter.minImports.increases (← getOptions) then
                      m!"by {newCumulImps - oldCumulImps} "
                    else
                      m!""
      Linter.logLint linter.minImports stx <|
        m!"Imports increased {byCount}to\n{currImpArray}\n\n\
          New imports: {new}\n" ++
            if redundant.isEmpty then m!"" else m!"\nNow redundant: {redundant}\n"
initialize addLinter minImportsLinter
end MinImports
end Mathlib.Linter