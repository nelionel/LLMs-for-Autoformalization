import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Basic
```
-/
namespace Mathlib.Tactic.Zify
open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic
```
`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : Nat) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
```
`zify` makes use of the `@[zify_simps]` attribute to move propositions,
and the `push_cast` tactic to simplify the `Int`-valued expressions.
`zify` is in some sense dual to the `lift` tactic.
`lift (z : Int) to Nat` will change the type of an
integer `z` (in the supertype) to `Nat` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `Int`.
`zify` changes propositions about `Nat` (the subtype) to propositions about `Int` (the supertype),
without changing the type of any variable.
-/
syntax (name := zify) "zify" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| zify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp -decide only [zify_simps, push_cast, $args,*] $[at $location]?)
def mkZifyContext (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic| simp -decide only [zify_simps, push_cast, $args,*])) false
def applySimpResultToProp' (proof : Expr) (prop : Expr) (r : Simp.Result) : MetaM (Expr × Expr) :=
  do
  match r.proof? with
  | some eqProof => return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
    if r.expr != prop then
      return (← mkExpectedTypeHint proof r.expr, r.expr)
    else
      return (proof, r.expr)
def zifyProof (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof : Expr) (prop : Expr) : TacticM (Expr × Expr) := do
  let ctx_result ← mkZifyContext simpArgs
  let (r, _) ← simp prop ctx_result.ctx
  applySimpResultToProp' proof prop r
@[zify_simps] lemma natCast_eq (a b : Nat) : a = b ↔ (a : Int) = (b : Int) := Int.ofNat_inj.symm
@[zify_simps] lemma natCast_le (a b : Nat) : a ≤ b ↔ (a : Int) ≤ (b : Int) := Int.ofNat_le.symm
@[zify_simps] lemma natCast_lt (a b : Nat) : a < b ↔ (a : Int) < (b : Int) := Int.ofNat_lt.symm
@[zify_simps] lemma natCast_ne (a b : Nat) : a ≠ b ↔ (a : Int) ≠ (b : Int) :=
  not_congr Int.ofNat_inj.symm
@[zify_simps] lemma natCast_dvd (a b : Nat) : a ∣ b ↔ (a : Int) ∣ (b : Int) := Int.ofNat_dvd.symm
@[deprecated (since := "2024-04-17")]
alias nat_cast_dvd := natCast_dvd
variable {R : Type*} [AddGroupWithOne R]
@[norm_cast] theorem Nat.cast_sub_of_add_le {m n k} (h : m + k ≤ n) :
    ((n - m : ℕ) : R) = n - m := Nat.cast_sub (m.le_add_right k |>.trans h)
@[norm_cast] theorem Nat.cast_sub_of_lt {m n} (h : m < n) :
    ((n - m : ℕ) : R) = n - m := Nat.cast_sub h.le
end Zify
end Mathlib.Tactic