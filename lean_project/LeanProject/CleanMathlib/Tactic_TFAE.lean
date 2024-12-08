import Qq
import Mathlib.Data.Nat.Notation
import Mathlib.Util.AtomM
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.ExtendDoc
namespace Mathlib.Tactic.TFAE
open Lean.Parser Term
namespace Parser
private def impTo : Parser := leading_parser unicodeSymbol " → " " -> "
private def impFrom : Parser := leading_parser unicodeSymbol " ← " " <- "
private def impIff : Parser := leading_parser unicodeSymbol " ↔ " " <-> "
private def impArrow : Parser := leading_parser impTo <|> impFrom <|> impIff
private def tfaeType := leading_parser num >> impArrow >> num
private def binder := leading_parser ppSpace >> binderIdent >> " : "
private def tfaeHaveIdLhs := leading_parser
  (binder <|> hygieneInfo)  >> tfaeType
private def tfaeHaveIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser
private def tfaeHaveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts
private def tfaeHavePatDecl  := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser
private def tfaeHaveDecl     := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdDecl <|> (ppSpace >> tfaeHavePatDecl) <|> tfaeHaveEqnsDecl
end Parser
open Parser
  tfae_have 2 → 1 := sorry 
  tfae_have 2 ↔ 3 := sorry 
  tfae_finish
```
All features of `have` are supported by `tfae_have`, including naming, matching,
destructuring, and goal creation. These are demonstrated below.
```lean4
example : TFAE [P, Q] := by
  tfae_have 1 → 2 := sorry
  tfae_have hpq : 1 → 2 := sorry
  tfae_have 1 → 2
  | p => f p
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry
  tfae_have h : 1 → 2 := f ?a
  ...
```
-/
syntax (name := tfaeHave) "tfae_have " tfaeHaveDecl : tactic
  tfae_have 2 → 1 := sorry 
  tfae_have 2 ↔ 3 := sorry 
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic
open List Lean Meta Expr Elab Tactic Mathlib.Tactic Qq
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR <|← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"
variable (hyps : Array (ℕ × ℕ × Expr)) (atoms : Array Q(Prop))
partial def dfs (i j : ℕ) (P P' : Q(Prop)) (hP : Q($P)) : StateT (Std.HashSet ℕ) MetaM Q($P') := do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P → $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure
def proveImpl (i j : ℕ) (P P' : Q(Prop)) : MetaM Q($P → $P') := do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
      mkLambdaFVars #[h] <|← dfs hyps atoms i j P P' h |>.run' {}
  catch _ =>
    throwError "couldn't prove {P} → {P'}"
partial def proveChain (i : ℕ) (is : List ℕ) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(Chain (· → ·) $P $l) := do
  match l with
  | ~q([]) => return q(Chain.nil)
  | ~q($P' :: $l') =>
    let i' :: is' := id is | unreachable!
    have cl' : Q(Chain (· → ·) $P' $l') := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(Chain.cons $p $cl')
partial def proveGetLastDImpl (i i' : ℕ) (is : List ℕ) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(getLastD $l $P' → $P) := do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'
def proveTFAE (is : List ℕ) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)
def mkTFAEId : TSyntax ``tfaeType → MacroM Name
  | `(tfaeType|$i:num $arr:impArrow $j:num) => do
    let arr ← match arr with
    | `(impArrow| ← ) => pure "from"
    | `(impArrow| → ) => pure "to"
    | `(impArrow| ↔ ) => pure "iff"
    | _ => Macro.throwUnsupported
    return .mkSimple <| String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]
  | _ => Macro.throwUnsupported
def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : MetaM ℕ := do
  let i' := i.getNat
  unless 1 ≤ i' && i' ≤ maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'
def elabTFAEType (tfaeList : List Q(Prop)) : TSyntax ``tfaeType → TermElabM Expr
  | stx@`(tfaeType|$i:num $arr:impArrow $j:num) => do
    let l := tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList.get! (i'-1)
    let Pj := tfaeList.get! (j'-1)
    Term.addTermInfo' i q(sorry : $Pi) Pi
    Term.addTermInfo' j q(sorry : $Pj) Pj
    let (ty : Q(Prop)) ← match arr with
      | `(impArrow| ← ) => pure q($Pj → $Pi)
      | `(impArrow| → ) => pure q($Pi → $Pj)
      | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
      | _ => throwUnsupportedSyntax
    Term.addTermInfo' stx q(sorry : $ty) ty
    return ty
  | _ => throwUnsupportedSyntax
macro_rules
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType := $val) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t := $val)
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType $alts:matchAlts) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t $alts)
open Term
elab_rules : tactic
| `(tfaeHave|tfae_have $d:tfaeHaveDecl) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  withRef d do
    match d with
    | `(tfaeHaveDecl| $b : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← exprToSyntax type) := $pf)
    | `(tfaeHaveDecl| $b : $t:tfaeType $alts:matchAlts) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← exprToSyntax type) $alts:matchAlts)
    | `(tfaeHaveDecl| $pat:term : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $pat:term : $(← exprToSyntax type) := $pf)
    | _ => throwUnsupportedSyntax
elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  goal.withContext do
    let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
    closeMainGoal `tfae_finish <|← AtomM.run .reducible do
      let is ← tfaeList.mapM (fun e ↦ Prod.fst <$> AtomM.addAtom e)
      let mut hyps := #[]
      for hyp in ← getLocalHyps do
        let ty ← whnfR <|← instantiateMVars <|← inferType hyp
        if let (``Iff, #[p1, p2]) := ty.getAppFnArgs then
          let (q1, _) ← AtomM.addAtom p1
          let (q2, _) ← AtomM.addAtom p2
          hyps := hyps.push (q1, q2, ← mkAppM ``Iff.mp #[hyp])
          hyps := hyps.push (q2, q1, ← mkAppM ``Iff.mpr #[hyp])
        else if ty.isArrow then
          let (q1, _) ← AtomM.addAtom ty.bindingDomain!
          let (q2, _) ← AtomM.addAtom ty.bindingBody!
          hyps := hyps.push (q1, q2, hyp)
      proveTFAE hyps (← get).atoms is tfaeListQ
end Mathlib.Tactic.TFAE
register_option Mathlib.Tactic.TFAE.useDeprecated : Bool := {
  descr := "Re-enable \"goal-style\" 'tfae_have' syntax"
  defValue := false
}
namespace Mathlib.Tactic.TFAE
open Lean Parser Meta Elab Tactic
@[inherit_doc tfaeHave]
syntax (name := tfaeHave') "tfae_have " tfaeHaveIdLhs : tactic
extend_docs tfaeHave'
  before "\"Goal-style\" `tfae_have` syntax is deprecated. Now, `tfae_have ...` should be followed\
    by  `:= ...`; see below for the new behavior. This warning can be turned off with \
    `set_option Mathlib.Tactic.TFAE.useDeprecated true`.\n\n***"
elab_rules : tactic
| `(tfaeHave'|tfae_have $d:tfaeHaveIdLhs) => withMainContext do
  let ref ← getRef
  unless useDeprecated.get (← getOptions) do
    logWarning <| .tagged ``Linter.deprecatedAttr m!"\
      \"Goal-style\" syntax '{ref}' is deprecated in favor of '{ref} := ...'.\n\n\
      To turn this warning off, use set_option Mathlib.Tactic.TFAE.useDeprecated true"
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  let (b, t) ← liftMacroM <| match d with
    | `(tfaeHaveIdLhs| $hy:hygieneInfo $t:tfaeType) => do
      pure (HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true), t)
    | `(tfaeHaveIdLhs| $b:ident : $t:tfaeType) =>
      pure (b, t)
    | _ => Macro.throwUnsupported
  let n := b.getId
  let type ← elabTFAEType tfaeList t
  let p ← mkFreshExprMVar type MetavarKind.syntheticOpaque n
  let (fv, mainGoal) ← (← MVarId.assert goal n type p).intro1P
  mainGoal.withContext do
    Term.addTermInfo' (isBinder := true) b (mkFVar fv)
  replaceMainGoal [p.mvarId!, mainGoal]
end TFAE
end Mathlib.Tactic