import Mathlib.Init
namespace Mathlib.Tactic.Substs
syntax (name := substs) "substs" (colGt ppSpace ident)* : tactic
macro_rules
| `(tactic| substs $xs:ident*) => `(tactic| ($[subst $xs]*))
end Substs
end Mathlib.Tactic