import Mathlib.Init
import Lean.HeadIndex
import Lean.Meta.ExprLens
import Lean.Meta.Check
namespace Lean.Meta
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app fn arg                  => visit fn pos.pushAppFn
                                    >=> visit arg pos.pushAppArg
      | .mdata _ expr                => visit expr pos
      | .proj _ _ struct             => visit struct pos.pushProj
      | .letE _ type value body _    => visit type pos.pushLetVarType
                                    >=> visit value pos.pushLetValue
                                    >=> visit body pos.pushLetBody
      | .lam _ binderType body _     => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | .forallE _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | _                            => pure
    if e.hasLooseBVars then
      visitChildren positions
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if ← isDefEq e p then
        setMCtx mctx 
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]
def viewKAbstractSubExpr (e : Expr) (pos : SubExpr.Pos) : MetaM (Option (Expr × Option Nat)) := do
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.indexOf? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))
def kabstractIsTypeCorrect (e subExpr : Expr) (pos : SubExpr.Pos) : MetaM Bool := do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
    isTypeCorrect (← replaceSubexpr (fun _ => pure fvar) pos e)
end Lean.Meta