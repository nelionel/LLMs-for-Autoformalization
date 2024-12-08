import Mathlib.Init
import Lean.Elab.Eval
import Lean.Elab.Tactic.ElabTerm
namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term
elab (name := applyWith) "apply" " (" &"config" " := " cfg:term ") " e:term : tactic => do
  let cfg ← unsafe evalTerm ApplyConfig (mkConst ``ApplyConfig) cfg
  evalApplyLikeTactic (·.apply · cfg) e
end Mathlib.Tactic