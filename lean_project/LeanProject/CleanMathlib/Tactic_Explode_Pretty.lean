import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
open Lean
namespace Mathlib.Explode
def padRight (mds : List MessageData) : MetaM (List MessageData) := do
  let mut maxLength := 0
  for md in mds do
    maxLength := max maxLength (← md.toString).length
  let pad (md : MessageData) : MetaM MessageData := do
    let padWidth : Nat := maxLength - (← md.toString).length
    return md ++ "".pushn ' ' padWidth
  mds.mapM pad
def rowToMessageData :
    List MessageData → List MessageData → List MessageData → List Entry → MetaM MessageData
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let pipes := String.join (List.replicate en.depth "│ ")
    let pipes := match en.status with
      | Status.sintro => s!"├ "
      | Status.intro  => s!"│ {pipes}┌ "
      | Status.cintro => s!"│ {pipes}├ "
      | Status.lam    => s!"│ {pipes}"
      | Status.reg    => s!"│ {pipes}"
    let row := m!"{line}│{dep}│ {thm} {pipes}{en.type}\n"
    return (← rowToMessageData lines deps thms es).compose row
  | _, _, _, _ => return MessageData.nil
def entriesToMessageData (entries : Entries) : MetaM MessageData := do
  let paddedLines ← padRight <| entries.l.map fun entry => m!"{entry.line!}"
  let paddedDeps ← padRight <| entries.l.map fun entry =>
    String.intercalate "," <| entry.deps.map (fun dep => (dep.map toString).getD "_")
  let paddedThms ← padRight <| entries.l.map (·.thm)
  rowToMessageData paddedLines paddedDeps paddedThms entries.l
end Explode
end Mathlib