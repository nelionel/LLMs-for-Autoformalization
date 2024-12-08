import Mathlib.Init
import Lean.Util.Path
open Lean System.FilePath
def getAllFiles (git : Bool) (ml : String) : IO (Array System.FilePath) := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  
  let allModules : Array System.FilePath ← (do
    if git then
      let mlDir := ml.push pathSeparator   
      let allLean ← IO.Process.run { cmd := "git", args := #["ls-files", mlDir ++ "*.lean"] }
      return (((allLean.dropRightWhile (· == '\n')).splitOn "\n").map (⟨·⟩)).toArray
    else do
      let all ← walkDir ml
      return all.filter (·.extension == some "lean"))
  return ← (allModules.erase ml.lean).filterMapM (fun f ↦ do
    if ← pathExists f then pure (some f) else pure none
  )
def getAllModulesSorted (git : Bool) (ml : String) : IO (Array String) := do
  let files ← getAllFiles git ml
  let names := ← files.mapM fun f => do
     return (← moduleNameOfFileName f none).toString
  return names.qsort (· < ·)