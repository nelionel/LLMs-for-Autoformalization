import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Density
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Core
namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
@[positivity Finset.card _]
def evalFinsetCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Finset.card $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assertInstancesCommute
    return .positive q(Finset.Nonempty.card_pos $ps)
  | _ => throwError "not Finset.card"
@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Fintype.card $β $instβ) =>
    let instβno ← synthInstanceQ q(Nonempty $β)
    assumeInstancesCommute
    return .positive q(@Fintype.card_pos $β $instβ $instβno)
  | _ => throwError "not Fintype.card"
@[positivity Finset.dens _]
def evalFinsetDens : PositivityExt where eval {u 𝕜} _ _ e := do
  match u, 𝕜, e with
  | 0, ~q(ℚ≥0), ~q(@Finset.dens $α $instα $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assumeInstancesCommute
    return .positive q(@Nonempty.dens_pos $α $instα $s $ps)
  | _, _, _ => throwError "not Finset.dens"
attribute [local instance] monadLiftOptionMetaM in
@[positivity Finset.sum _ _]
def evalFinsetSum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.sum $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) := ← (do
      let .positive pbody := rbody | pure none 
      let .some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(OrderedCancelAddCommMonoid $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      return some q(@sum_pos $ι $α $pα' $f $s (fun i _ ↦ $pr i) $ps))
    if let some p_pos := p_pos then
      return .positive p_pos
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let pα' ← synthInstanceQ q(OrderedAddCommMonoid $α)
      assertInstancesCommute
      return .nonnegative q(@sum_nonneg $ι $α $pα' $f $s fun i _ ↦ $pr i)
  | _ => throwError "not Finset.sum"
variable {α : Type*} {s : Finset α}
example : 0 ≤ #s := by positivity
example (hs : s.Nonempty) : 0 < #s := by positivity
variable [Fintype α]
example : 0 ≤ Fintype.card α := by positivity
example : 0 ≤ dens s := by positivity
example (hs : s.Nonempty) : 0 < dens s := by positivity
example (hs : s.Nonempty) : dens s ≠ 0 := by positivity
example [Nonempty α] : 0 < #(univ : Finset α) := by positivity
example [Nonempty α] : 0 < Fintype.card α := by positivity
example [Nonempty α] : 0 < dens (univ : Finset α) := by positivity
example [Nonempty α] : dens (univ : Finset α) ≠ 0 := by positivity
example {G : Type*} {A : Finset G} :
  let f := fun _ : G ↦ 1; (∀ s, f s ^ 2 = 1) → 0 ≤ #A := by
  intros
  positivity 
end Mathlib.Meta.Positivity