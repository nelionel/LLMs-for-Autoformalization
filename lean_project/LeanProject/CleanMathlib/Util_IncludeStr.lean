import Mathlib.Init
namespace Mathlib.Util
elab (name := includeStr) "include_str " str:str : term => do
  let some str := str.1.isStrLit? | Lean.Elab.throwUnsupportedSyntax
  let srcPath := System.FilePath.mk (← Lean.MonadLog.getFileName)
  let some srcDir := srcPath.parent | throwError "{srcPath} not in a valid directory"
  let path := srcDir / str
  Lean.mkStrLit <$> IO.FS.readFile path
end Mathlib.Util