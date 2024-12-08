import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
#guard_msgs in
attribute [-instance] instAddNat in
#synth Add Nat
#guard_msgs in
#synth Add Nat
@[simp]
theorem what : False := sorry
#guard_msgs in
attribute [-simp] what in
example : False := by simp
#guard_msgs in
example : False := by simp
```
-/
open Lean Elab Command
namespace Mathlib.Linter
register_option linter.globalAttributeIn : Bool := {
  defValue := true
  descr := "enable the globalAttributeIn linter"
}
namespace globalAttributeInLinter
def getLinterGlobalAttributeIn (o : Options) : Bool :=
  Linter.getLinterValue linter.globalAttributeIn o
def getGlobalAttributesIn? : Syntax → Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default
def globalAttributeIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterGlobalAttributeIn (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let .some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.globalAttributeIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local {attr}`"
initialize addLinter globalAttributeIn
end globalAttributeInLinter
end Mathlib.Linter