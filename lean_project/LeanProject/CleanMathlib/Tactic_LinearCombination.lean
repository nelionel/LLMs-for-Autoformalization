import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Compare
namespace Mathlib.Tactic.LinearCombination
open Lean
open Elab Meta Term Mathlib Ineq
inductive Expanded
  | proof (rel : Ineq) (pf : Syntax.Term)
  | const (c : Syntax.Term)
def rescale (lems : Ineq.WithStrictness → Name) (ty : Option Expr) (p c : Term) :
    Ineq → TermElabM Expanded
  | eq => do
    let i := mkIdent <| lems .eq
    .proof eq <$> ``($i $p $c)
  | le => do
    let i := mkIdent <| lems .le
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let hc₂ ← Meta.Positivity.proveNonneg e₂
    .proof le <$> ``($i $p $(← hc₂.toSyntax))
  | lt => do
    let e₂ ← withSynthesizeLight <| Term.elabTerm c ty
    let (strict, hc₂) ← Meta.Positivity.bestResult e₂
    let i := mkIdent <| lems (.lt strict)
    let p' : Term ← ``($i $p $(← hc₂.toSyntax))
    if strict then pure (.proof lt p') else pure (.proof le p')
partial def expandLinearCombo (ty : Option Expr) (stx : Syntax.Term) :
    TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof rel₁ p₁, .proof rel₂ p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ rel₂
      .proof (max rel₁ rel₂) <$> ``($i $p₁ $p₂)
    | .proof rel p, .const c | .const c, .proof rel p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof rel p, .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      pure (.proof rel p)
    | .const c, .proof eq p =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      .proof eq <$> ``(Eq.symm $p)
    | .proof rel₁ p₁, .proof eq p₂ =>
      let i := mkIdent <| Ineq.addRelRelData rel₁ eq
      .proof rel₁ <$> ``($i $p₁ (Eq.symm $p₂))
    | _, .proof _ _ =>
      throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `(-$e) => do
      match ← expandLinearCombo ty e with
      | .const c => .const <$> `(-$c)
      | .proof eq p => .proof eq <$> ``(Eq.symm $p)
      | .proof _ _ =>
        throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `($e₁ *%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale mulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale mulConstRelData ty p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ •%$tk $e₂) => do
    match ← expandLinearCombo none e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ • $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale smulRelConstData ty p₁ c₂ rel₁
    | .const c₁, .proof rel₂ p₂ => rescale smulConstRelData none p₂ c₁ rel₂
    | .proof _ _, .proof _ _ =>
      throwErrorAt tk "'linear_combination' supports only linear operations"
  | `($e₁ /%$tk $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof rel₁ p₁, .const c₂ => rescale divRelConstData ty p₁ c₂ rel₁
    | _, .proof _ _ => throwErrorAt tk "'linear_combination' supports only linear operations"
  | e =>
    withSynthesize do
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      match ← try? (← inferType c).ineq? with
      | some (rel, _) => .proof rel <$> c.toSyntax
      | none => .const <$> c.toSyntax
def elabLinearCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext <| Tactic.focus do
  let eType ← withReducible <| (← Tactic.getMainGoal).getType'
  let (goalRel, ty, _) ← eType.ineq?
  let (hypRel, p) ← match input with
  | none => Prod.mk eq <$>  `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const c =>
      logWarningAt c "this constant has no effect on the linear combination; it can be dropped \
        from the term"
      Prod.mk eq <$> `(Eq.refl 0)
    | .proof hypRel p => pure (hypRel, p)
  let (reduceLem, newGoalRel) : Name × Ineq := ← do
    match Ineq.relImpRelData hypRel goalRel with
    | none => throwError "cannot prove an equality from inequality hypotheses"
    | some n => pure n
  let p' ← do
    match exp? with
    | some n =>
      if n.getNat = 1 then
        `($(mkIdent reduceLem) $p ?a)
      else
        match hypRel with
        | eq => `(eq_of_add_pow $n $p ?a)
        | _ => throwError
          "linear_combination tactic not implemented for exponentiation of inequality goals"
    | _ => `($(mkIdent reduceLem) $p ?a)
  Term.withoutErrToSorry <| Tactic.refineCore p' `refine false
  let _ ← Tactic.tryTactic <| Tactic.liftMetaTactic fun g ↦ g.applyConst newGoalRel.rearrangeData
  match norm? with
  | some norm => Tactic.evalTactic norm
  | none => withRef tk <| Tactic.liftMetaFinishingTactic <|
    match newGoalRel with
    | eq => fun g ↦ AtomM.run .instances <| Ring.proveEq g
    | le => Ring.proveLE
    | lt => Ring.proveLT
syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"
syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"
syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tk tac n e
end Mathlib.Tactic.LinearCombination