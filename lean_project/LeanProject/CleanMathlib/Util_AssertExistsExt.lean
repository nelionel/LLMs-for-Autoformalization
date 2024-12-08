import Lean.Environment
import Mathlib.Init
open Lean
namespace Mathlib.AssertNotExist
structure AssertExists where
  isDecl : Bool
  givenName : Name
  modName : Name
  deriving BEq, Hashable
initialize assertExistsExt : SimplePersistentEnvExtension AssertExists (Std.HashSet AssertExists) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }
def addDeclEntry {m : Type → Type} [MonadEnv m] (isDecl : Bool) (declName mod : Name) : m Unit :=
  modifyEnv (assertExistsExt.addEntry · { isDecl := isDecl, givenName := declName, modName := mod })
end Mathlib.AssertNotExist
open Mathlib.AssertNotExist
def Lean.Environment.getSortedAssertExists (env : Environment) : Array AssertExists :=
  assertExistsExt.getState env |>.toArray.qsort fun d e => (e.isDecl < d.isDecl) ||
    (e.isDecl == d.isDecl && (d.givenName.toString < e.givenName.toString))