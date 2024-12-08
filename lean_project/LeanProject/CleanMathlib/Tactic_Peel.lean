import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Basic
namespace Mathlib.Tactic.Peel
open Lean Expr Meta Elab Tactic
syntax (name := peel)
  "peel" (num)? (ppSpace colGt term)?
  (" with" (ppSpace colGt (ident <|> hole))+)? (usingArg)? : tactic
private lemma and_imp_left_of_imp_imp {p q r : Prop} (h : r → p → q) : r ∧ p → r ∧ q := by tauto
private theorem eventually_imp {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x → q x) (hp : ∀ᶠ (x : α) in f, p x) : ∀ᶠ (x : α) in f, q x :=
  Filter.Eventually.mp hp (Filter.Eventually.of_forall hq)
private theorem frequently_imp {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x → q x) (hp : ∃ᶠ (x : α) in f, p x) : ∃ᶠ (x : α) in f, q x :=
  Filter.Frequently.mp hp (Filter.Eventually.of_forall hq)
private theorem eventually_congr {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x ↔ q x) : (∀ᶠ (x : α) in f, p x) ↔ ∀ᶠ (x : α) in f, q x := by
  congr! 2; exact hq _
private theorem frequently_congr {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x ↔ q x) : (∃ᶠ (x : α) in f, p x) ↔ ∃ᶠ (x : α) in f, q x := by
  congr! 2; exact hq _
def quantifiers : List Name :=
  [``Exists, ``And, ``Filter.Eventually, ``Filter.Frequently]
def whnfQuantifier (p : Expr) (unfold : Bool) : MetaM Expr := do
  if unfold then
    whnfHeadPred p fun e =>
      if let .const n .. := e.getAppFn then
        return !(n ∈ quantifiers)
      else
        return false
  else
    whnfR p
def throwPeelError {α : Type} (ty target : Expr) : MetaM α :=
  throwError "Tactic 'peel' could not match quantifiers in{indentD ty}\nand{indentD target}"
def mkFreshBinderName (f : Expr) : MetaM Name :=
  mkFreshUserName (if let .lam n .. := f then n else `a)
def applyPeelThm (thm : Name) (goal : MVarId)
    (e : Expr) (ty target : Expr) (n : Name) (n' : Name) :
    MetaM (FVarId × List MVarId) := do
  let new_goal :: ge :: _ ← goal.applyConst thm <|> throwPeelError ty target
    | throwError "peel: internal error"
  ge.assignIfDefeq e <|> throwPeelError ty target
  let (fvars, new_goal) ← new_goal.introN 2 [n, n']
  return (fvars[1]!, [new_goal])
def peelCore (goal : MVarId) (e : Expr) (n? : Option Name) (n' : Name) (unfold : Bool) :
    MetaM (FVarId × List MVarId) := goal.withContext do
  let ty ← whnfQuantifier (← inferType e) unfold
  let target ← whnfQuantifier (← goal.getType) unfold
  if ty.isForall && target.isForall then
    applyPeelThm ``forall_imp goal e ty target (← n?.getDM (mkFreshUserName target.bindingName!)) n'
  else if ty.getAppFn.isConst
            && ty.getAppNumArgs == target.getAppNumArgs
            && ty.getAppFn == target.getAppFn then
    match target.getAppFnArgs with
    | (``Exists, #[_, p]) =>
      applyPeelThm ``Exists.imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``And, #[_, _]) =>
      applyPeelThm ``and_imp_left_of_imp_imp goal e ty target (← n?.getDM (mkFreshUserName `p)) n'
    | (``Filter.Eventually, #[_, p, _]) =>
      applyPeelThm ``eventually_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``Filter.Frequently, #[_, p, _]) =>
      applyPeelThm ``frequently_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | _ => throwPeelError ty target
  else
    throwPeelError ty target
def peelArgs (e : Expr) (num : Nat) (l : List Name) (n? : Option Name) (unfold : Bool := true) :
    TacticM Unit := do
  match num with
    | 0 => return
    | num + 1 =>
      let fvarId ← liftMetaTacticAux (peelCore · e l.head? (n?.getD `this) unfold)
      peelArgs (.fvar fvarId) num l.tail n?
      unless num == 0 do
        if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
          replaceMainGoal [mvarId]
partial def peelUnbounded (e : Expr) (n? : Option Name) (unfold : Bool := false) :
    TacticM Bool := do
  let fvarId? ← observing? <| liftMetaTacticAux (peelCore · e none (n?.getD `this) unfold)
  if let some fvarId := fvarId? then
    let peeled ← peelUnbounded (.fvar fvarId) n?
    if peeled then
      if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
        replaceMainGoal [mvarId]
    return true
  else
    return false
def peelIffAux : TacticM Unit := do
  evalTactic (← `(tactic| focus
    first | apply forall_congr'
          | apply exists_congr
          | apply eventually_congr
          | apply frequently_congr
          | apply and_congr_right
          | fail "failed to apply a quantifier congruence lemma."))
def peelArgsIff (l : List Name) : TacticM Unit := withMainContext do
  match l with
    | [] => pure ()
    | h :: hs =>
      peelIffAux
      let goal ← getMainGoal
      let (_, new_goal) ← goal.intro h
      replaceMainGoal [new_goal]
      peelArgsIff hs
elab_rules : tactic
  | `(tactic| peel $[$num?:num]? $e:term $[with $l?* $n?]?) => withMainContext do
    let e ← elabTermForApply e false
    let n? := n?.bind fun n => if n.raw.isIdent then pure n.raw.getId else none
    let l := (l?.getD #[]).map getNameOfIdent' |>.toList
    let num? := num?.map (·.getNat) <|> if l.isEmpty then none else l.length
    if let some num := num? then
      peelArgs e num l n?
    else
      unless ← peelUnbounded e n? do
        throwPeelError (← inferType e) (← getMainTarget)
  | `(tactic| peel $n:num) => peelArgsIff <| .replicate n.getNat `_
  | `(tactic| peel with $args*) => peelArgsIff (args.map getNameOfIdent').toList
macro_rules
  | `(tactic| peel $[$n:num]? $[$e:term]? $[with $h*]? using $u:term) =>
    `(tactic| peel $[$n:num]? $[$e:term]? $[with $h*]?; exact $u)
end Mathlib.Tactic.Peel