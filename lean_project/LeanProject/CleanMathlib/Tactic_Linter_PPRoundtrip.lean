import Lean.Elab.Command
import Mathlib.Init
open Lean Elab Command
namespace Mathlib.Linter
register_option linter.ppRoundtrip : Bool := {
  defValue := false
  descr := "enable the ppRoundtrip linter"
}
def polishPP (s : String) : String :=
  let s := s.split (·.isWhitespace)
  (" ".intercalate (s.filter (!·.isEmpty)))
    |>.replace "
def polishSource (s : String) : String × Array Nat :=
  let split := s.split (· == '\n')
  let preWS := split.foldl (init := #[]) fun p q =>
    let txt := q.trimLeft.length
    (p.push (q.length - txt)).push txt
  let preWS := preWS.eraseIdxIfInBounds 0
  let s := (split.map .trimLeft).filter (· != "")
  (" ".intercalate (s.filter (!·.isEmpty)), preWS)
def posToShiftedPos (lths : Array Nat) (diff : Nat) : Nat := Id.run do
  let mut (ws, noWS) := (diff, 0)
  for con in [:lths.size / 2] do
    let curr := lths[2 * con]!
    if noWS + curr < diff then
      noWS := noWS + curr
      ws := ws + lths[2 * con + 1]!
    else
      break
  return ws
def zoomString (str : String) (centre offset : Nat) : Substring :=
  { str := str, startPos := ⟨centre - offset⟩, stopPos := ⟨centre + offset⟩ }
def capSourceInfo (s : SourceInfo) (p : Nat) : SourceInfo :=
  match s with
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos := ⟨min endPos.1 p⟩} ⟨min endPos.1 p⟩
    | .synthetic pos endPos canonical =>
      .synthetic pos ⟨min endPos.1 p⟩ canonical
    | .none => s
partial
def capSyntax (stx : Syntax) (p : Nat) : Syntax :=
  match stx with
    | .node si k args => .node (capSourceInfo si p) k (args.map (capSyntax · p))
    | .atom si val => .atom (capSourceInfo si p) (val.take p)
    | .ident si r v pr => .ident (capSourceInfo si p) { r with stopPos := ⟨min r.stopPos.1 p⟩ } v pr
    | s => s
namespace PPRoundtrip
@[inherit_doc Mathlib.Linter.linter.ppRoundtrip]
def ppRoundtrip : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.ppRoundtrip (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let stx := capSyntax stx (stx.getTailPos?.getD default).1
    let origSubstring := stx.getSubstring?.getD default
    let (real, lths) := polishSource origSubstring.toString
    let fmt ← (liftCoreM do PrettyPrinter.ppCategory `command stx <|> (do
      Linter.logLint linter.ppRoundtrip stx
        m!"The ppRoundtrip linter had some parsing issues: \
           feel free to silence it with `set_option linter.ppRoundtrip false in` \
           and report this error!"
      return real))
    let st := polishPP fmt.pretty
    if st != real then
      let diff := real.firstDiffPos st
      let pos := posToShiftedPos lths diff.1 + origSubstring.startPos.1
      let f := origSubstring.str.drop (pos)
      let extraLth := (f.takeWhile (· != st.get diff)).length
      let srcCtxt := zoomString real diff.1 5
      let ppCtxt  := zoomString st diff.1 5
      Linter.logLint linter.ppRoundtrip (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
        m!"source context\n'{srcCtxt}'\n'{ppCtxt}'\npretty-printed context"
initialize addLinter ppRoundtrip
end Mathlib.Linter.PPRoundtrip