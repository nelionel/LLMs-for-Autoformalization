import Mathlib.Tactic.Core
import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic
open Lean.Meta
namespace Lean.Elab.Tactic
def getMemType {m : Type → Type} [Monad m] [MonadError m] (e : Expr) : m (Option Expr) := do
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, type, _, _, _]) =>
    match type.getAppFnArgs with
    | (``List, #[α])     => return α
    | (``Multiset, #[α]) => return α
    | (``Finset, #[α])   => return α
    | _ => throwError "Hypothesis must be of type `x ∈ (A : List α)`, `x ∈ (A : Finset α)`, \
                       or `x ∈ (A : Multiset α)`"
  | _ => return none
partial def unfoldCases (g : MVarId) (h : FVarId)
    (userNamePre : Name := .anonymous) (counter := 0) : MetaM (List MVarId) := do
  let gs ← g.cases h
  try
    let #[g₁, g₂] := gs | throwError "unexpected number of cases"
    g₁.mvarId.setUserName (.str userNamePre s!"{counter}")
    let gs ← unfoldCases g₂.mvarId g₂.fields[2]!.fvarId! userNamePre (counter+1)
    return g₁.mvarId :: gs
  catch _ => return []
partial def finCasesAt (g : MVarId) (hyp : FVarId) : MetaM (List MVarId) := g.withContext do
  let type ← hyp.getType >>= instantiateMVars
  match ← getMemType type with
  | some _ => unfoldCases g hyp (userNamePre := ← g.getTag)
  | none =>
    let inst ← synthInstance (← mkAppM ``Fintype #[type])
    let elems ← mkAppOptM ``Fintype.elems #[type, inst]
    let t ← mkAppM ``Membership.mem #[elems, .fvar hyp]
    let v ← mkAppOptM ``Fintype.complete #[type, inst, Expr.fvar hyp]
    let (fvar, g) ← (← g.assert `this t v).intro1P
    finCasesAt g fvar
syntax (name := finCases) "fin_cases " ("*" <|> term,+) (" with " term,+)? : tactic
@[tactic finCases] elab_rules : tactic
  | `(tactic| fin_cases $[$hyps:ident],*) => withMainContext <| focus do
    for h in hyps do
      allGoals <| liftMetaTactic (finCasesAt · (← getFVarId h))
end Tactic
end Elab
end Lean