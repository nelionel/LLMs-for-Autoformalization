import Mathlib.Init
namespace Lean.Elab.Command
def resolveNamespace (ns : Name) : Name → Name
  | `_root_ => Name.anonymous
  | Name.str n s .. => Name.mkStr (resolveNamespace ns n) s
  | Name.num n i .. => Name.mkNum (resolveNamespace ns n) i
  | Name.anonymous => ns
def withWeakNamespace {α : Type} (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  let ns := resolveNamespace old ns
  modify fun s ↦ { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })
elab "with_weak_namespace " ns:ident cmd:command : command =>
  withWeakNamespace ns.getId (elabCommand cmd)
end Lean.Elab.Command