import Mathlib.Logic.Basic
import Mathlib.Data.Option.Defs
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.CC.Datatypes
import Mathlib.Tactic.CC.Lemmas
import Batteries.Data.RBMap.Alter
universe u
open Lean Meta Elab Tactic Std
namespace Mathlib.Tactic.CC
initialize
  registerTraceClass `Meta.Tactic.cc.merge
  registerTraceClass `Meta.Tactic.cc.failure
  registerTraceClass `Debug.Meta.Tactic.cc
  registerTraceClass `Debug.Meta.Tactic.cc.ac
  registerTraceClass `Debug.Meta.Tactic.cc.parentOccs
abbrev CCM := StateRefT CCStructure MetaM
namespace CCM
@[inline]
def run {α : Type} (x : CCM α) (c : CCStructure) : MetaM (α × CCStructure) := StateRefT'.run x c
@[inline]
def modifyTodo (f : Array TodoEntry → Array TodoEntry) : CCM Unit :=
  modify fun cc => { cc with todo := f cc.todo }
@[inline]
def modifyACTodo (f : Array ACTodoEntry → Array ACTodoEntry) : CCM Unit :=
  modify fun cc => { cc with acTodo := f cc.acTodo }
@[inline]
def modifyCache (f : CCCongrTheoremCache → CCCongrTheoremCache) : CCM Unit :=
  modify fun cc => { cc with cache := f cc.cache }
@[inline]
def getTodo : CCM (Array TodoEntry) := do
  return (← get).todo
@[inline]
def getACTodo : CCM (Array ACTodoEntry) := do
  return (← get).acTodo
@[inline]
def getCache : CCM CCCongrTheoremCache := do
  return (← get).cache
def getEntry (e : Expr) : CCM (Option Entry) := do
  return (← get).entries.find? e
def normalize (e : Expr) : CCM Expr := do
  if let some normalizer := (← get).normalizer then
    normalizer.normalize e
  else
    return e
def pushTodo (lhs rhs : Expr) (H : EntryExpr) (heqProof : Bool) : CCM Unit := do
  modifyTodo fun todo => todo.push (lhs, rhs, H, heqProof)
@[inline]
def pushEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  pushTodo lhs rhs H false
@[inline]
def pushHEq (lhs rhs : Expr) (H : EntryExpr) : CCM Unit :=
  pushTodo lhs rhs H true
@[inline]
def pushReflEq (lhs rhs : Expr) : CCM Unit :=
  pushEq lhs rhs .refl
def getRoot (e : Expr) : CCM Expr := do
  return (← get).root e
def isCgRoot (e : Expr) : CCM Bool := do
  return (← get).isCgRoot e
def addOccurrence (parent child : Expr) (symmTable : Bool) : CCM Unit := do
  let childRoot ← getRoot child
  modify fun ccs =>
    { ccs with
      parents := ccs.parents.alter childRoot fun ps? =>
        let ps := ps?.getD ∅
        ps.insert { expr := parent, symmTable } }
partial def isCongruent (e₁ e₂ : Expr) : CCM Bool := do
  let .app f a := e₁ | failure
  let .app g b := e₂ | failure
  if (← getEntry e₁).any Entry.fo then
    e₁.withApp fun f₁ args₁ =>
    e₂.withApp fun f₂ args₂ => do
      if ha : args₁.size = args₂.size then
        for hi : i in [:args₁.size] do
          if (← getRoot (args₁[i]'hi.2)) != (← getRoot (args₂[i]'(ha.symm ▸ hi.2))) then
            return false
        if f₁ == f₂ then return true
        else if (← getRoot f₁) != (← getRoot f₂) then
          return false
        else if ← pureIsDefEq (← inferType f₁) (← inferType f₂) then
          return true
        else return false
      else return false
  else
    if (← getRoot a) != (← getRoot b) then
      return false
    else if (← getRoot f) != (← getRoot g) then
      return false
    else if ← pureIsDefEq (← inferType f) (← inferType g) then
      return true
    else if f.isApp && g.isApp then
      isCongruent f g
    else
      return false
def mkCongruencesKey (e : Expr) : CCM CongruencesKey := do
  let .app f a := e | failure
  if (← getEntry e).any Entry.fo then
    e.withApp fun fn args => do
      return .fo (← getRoot fn) (← args.mapM getRoot)
  else
    return .ho (← getRoot f) (← getRoot a)
def mkSymmCongruencesKey (lhs rhs : Expr) : CCM SymmCongruencesKey := do
  let lhs ← getRoot lhs
  let rhs ← getRoot rhs
  if hash lhs > hash rhs then return { h₁ := rhs, h₂ := lhs } else return { h₁ := lhs, h₂ := rhs }
def mkCCHCongrTheorem (fn : Expr) (nargs : Nat) : CCM (Option CCCongrTheorem) := do
  let cache ← getCache
  let key₁ : CCCongrTheoremKey := { fn, nargs }
  if let some it := cache[key₁]? then
    return it
  let lemm ← mkCCHCongrWithArity fn nargs
  if let some lemm := lemm then
    modifyCache fun ccc => ccc.insert key₁ (some lemm)
    return lemm
  modifyCache fun ccc => ccc.insert key₁ none
  return none
def mkCCCongrTheorem (e : Expr) : CCM (Option CCCongrTheorem) := do
  let fn := e.getAppFn
  let nargs := e.getAppNumArgs
  mkCCHCongrTheorem fn nargs
def propagateInstImplicit (e : Expr) : CCM Unit := do
  let type ← inferType e
  let type ← normalize type
  match (← get).instImplicitReprs.find? type with
  | some l =>
    for e' in l do
      if ← pureIsDefEq e e' then
        pushReflEq e e'
        return
    modify fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type (e :: l) }
  | none =>
    modify fun ccs =>
      { ccs with instImplicitReprs := ccs.instImplicitReprs.insert type [e] }
def setFO (e : Expr) : CCM Unit :=
  modify fun ccs =>
    { ccs with entries := ccs.entries.modify e fun d => { d with fo := true } }
partial def updateMT (e : Expr) : CCM Unit := do
  let r ← getRoot e
  let some ps := (← get).parents.find? r | return
  for p in ps do
    let some it ← getEntry p.expr | failure
    let gmt := (← get).gmt
    if it.mt < gmt then
      let newIt := { it with mt := gmt }
      modify fun ccs =>
        { ccs with entries := ccs.entries.insert p.expr newIt }
      updateMT p.expr
def hasHEqProofs (root : Expr) : CCM Bool := do
  let some n ← getEntry root | failure
  guard (n.root == root)
  return n.heqProofs
def flipProofCore (H : Expr) (flipped heqProofs : Bool) : CCM Expr := do
  let mut newH := H
  if ← liftM <| pure heqProofs <&&> Expr.isEq <$> (inferType H >>= whnf) then
    newH ← mkAppM ``heq_of_eq #[H]
  if !flipped then
    return newH
  else if heqProofs then
    mkHEqSymm newH
  else
    mkEqSymm newH
def flipDelayedProofCore (H : DelayedExpr) (flipped heqProofs : Bool) : CCM DelayedExpr := do
  let mut newH := H
  if heqProofs then
    newH := .heqOfEq H
  if !flipped then
    return newH
  else if heqProofs then
    return .heqSymm newH
  else
    return .eqSymm newH
def flipProof (H : EntryExpr) (flipped heqProofs : Bool) : CCM EntryExpr :=
  match H with
  | .ofExpr H => EntryExpr.ofExpr <$> flipProofCore H flipped heqProofs
  | .ofDExpr H => EntryExpr.ofDExpr <$> flipDelayedProofCore H flipped heqProofs
  | _ => return H
def isEqv (e₁ e₂ : Expr) : CCM Bool := do
  let some n₁ ← getEntry e₁ | return false
  let some n₂ ← getEntry e₂ | return false
  return n₁.root == n₂.root
def isNotEqv (e₁ e₂ : Expr) : CCM Bool := do
  let tmp ← mkEq e₁ e₂
  if ← isEqv tmp (.const ``False []) then return true
  let tmp ← mkHEq e₁ e₂
  isEqv tmp (.const ``False [])
@[inline]
def isEqTrue (e : Expr) : CCM Bool :=
  isEqv e (.const ``True [])
@[inline]
def isEqFalse (e : Expr) : CCM Bool :=
  isEqv e (.const ``False [])
def mkTrans (H₁ H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  if heqProofs then mkHEqTrans H₁ H₂ else mkEqTrans H₁ H₂
def mkTransOpt (H₁? : Option Expr) (H₂ : Expr) (heqProofs : Bool) : MetaM Expr :=
  match H₁? with
  | some H₁ => mkTrans H₁ H₂ heqProofs
  | none => pure H₂
mutual
partial def mkCongrProofCore (lhs rhs : Expr) (heqProofs : Bool) : CCM Expr := do
  let mut lhsArgsRev : Array Expr := #[]
  let mut rhsArgsRev : Array Expr := #[]
  let mut lhsIt := lhs
  let mut rhsIt := rhs
  if lhs != rhs then
    repeat
      let .app lhsItFn lhsItArg := lhsIt | failure
      let .app rhsItFn rhsItArg := rhsIt | failure
      lhsArgsRev := lhsArgsRev.push lhsItArg
      rhsArgsRev := rhsArgsRev.push rhsItArg
      lhsIt := lhsItFn
      rhsIt := rhsItFn
      if lhsIt == rhsIt then
        break
      if ← pureIsDefEq lhsIt rhsIt then
        break
      if ← isEqv lhsIt rhsIt <&&>
          inferType lhsIt >>= fun i₁ => inferType rhsIt >>= fun i₂ => pureIsDefEq i₁ i₂ then
        break
  if lhsArgsRev.isEmpty then
    if heqProofs then
      return (← mkHEqRefl lhs)
    else
      return (← mkEqRefl lhs)
  let lhsArgs := lhsArgsRev.reverse
  let rhsArgs := rhsArgsRev.reverse
  let PLift.up ha ← if ha : lhsArgs.size = rhsArgs.size then pure (PLift.up ha) else failure
  let lhsFn := lhsIt
  let rhsFn := rhsIt
  guard (← isEqv lhsFn rhsFn <||> pureIsDefEq lhsFn rhsFn)
  guard (← pureIsDefEq (← inferType lhsFn) (← inferType rhsFn))
  let some specLemma ← mkCCHCongrTheorem lhsFn lhsArgs.size | failure
  let mut kindsIt := specLemma.argKinds
  let mut lemmaArgs : Array Expr := #[]
  for hi : i in [:lhsArgs.size] do
    guard !kindsIt.isEmpty
    lemmaArgs := lemmaArgs.push (lhsArgs[i]'hi.2) |>.push (rhsArgs[i]'(ha.symm ▸ hi.2))
    if kindsIt[0]! matches CongrArgKind.heq then
      let some p ← getHEqProof (lhsArgs[i]'hi.2) (rhsArgs[i]'(ha.symm ▸ hi.2)) | failure
      lemmaArgs := lemmaArgs.push p
    else
      guard (kindsIt[0]! matches .eq)
      let some p ← getEqProof (lhsArgs[i]'hi.2) (rhsArgs[i]'(ha.symm ▸ hi.2)) | failure
      lemmaArgs := lemmaArgs.push p
    kindsIt := kindsIt.eraseIdx! 0
  let mut r := mkAppN specLemma.proof lemmaArgs
  if specLemma.heqResult && !heqProofs then
    r ← mkAppM ``eq_of_heq #[r]
  else if !specLemma.heqResult && heqProofs then
    r ← mkAppM ``heq_of_eq #[r]
  if ← pureIsDefEq lhsFn rhsFn then
    return r
  let some lhsFnEqRhsFn ← getEqProof lhsFn rhsFn | failure
  let motive ←
    withLocalDeclD `x (← inferType lhsFn) fun x => do
      let motiveRhs := mkAppN x rhsArgs
      let motive ← if heqProofs then mkHEq lhs motiveRhs else mkEq lhs motiveRhs
      let hType ← mkEq lhsFn x
      withLocalDeclD `h hType fun h =>
        mkLambdaFVars #[x, h] motive
  mkEqRec motive r lhsFnEqRhsFn
partial def mkSymmCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM (Option Expr) := do
  let some (R₁, lhs₁, rhs₁) ← e₁.relSidesIfSymm? | return none
  let some (R₂, lhs₂, rhs₂) ← e₂.relSidesIfSymm? | return none
  if R₁ != R₂ then return none
  if (← isEqv lhs₁ lhs₂) then
    return none
  guard (← isEqv lhs₁ rhs₂)
  let newE₁ ← mkRel R₁ rhs₁ lhs₁
  let e₁IffNewE₁ ←
    withLocalDeclD `h₁ e₁ fun h₁ =>
    withLocalDeclD `h₂ newE₁ fun h₂ => do
      mkAppM ``Iff.intro
        #[← mkLambdaFVars #[h₁] (← h₁.applySymm), ← mkLambdaFVars #[h₂] (← h₂.applySymm)]
  let mut e₁EqNewE₁ := mkApp3 (.const ``propext []) e₁ newE₁ e₁IffNewE₁
  let newE₁EqE₂ ← mkCongrProofCore newE₁ e₂ heqProofs
  if heqProofs then
    e₁EqNewE₁ ← mkAppM ``heq_of_eq #[e₁EqNewE₁]
  return some (← mkTrans e₁EqNewE₁ newE₁EqE₂ heqProofs)
partial def mkCongrProof (e₁ e₂ : Expr) (heqProofs : Bool) : CCM Expr := do
  if let some r ← mkSymmCongrProof e₁ e₂ heqProofs then
    return r
  else
    mkCongrProofCore e₁ e₂ heqProofs
partial def mkDelayedProof (H : DelayedExpr) : CCM Expr := do
  match H with
  | .ofExpr H => return H
  | .eqProof lhs rhs => liftOption (← getEqProof lhs rhs)
  | .congrArg f h => mkCongrArg f (← mkDelayedProof h)
  | .congrFun h a => mkCongrFun (← mkDelayedProof h) (← liftOption a.toExpr)
  | .eqSymm h => mkEqSymm (← mkDelayedProof h)
  | .eqSymmOpt a₁ a₂ h =>
    mkAppOptM ``Eq.symm #[none, ← liftOption a₁.toExpr, ← liftOption a₂.toExpr, ← mkDelayedProof h]
  | .eqTrans h₁ h₂ => mkEqTrans (← mkDelayedProof h₁) (← mkDelayedProof h₂)
  | .eqTransOpt a₁ a₂ a₃ h₁ h₂ =>
    mkAppOptM ``Eq.trans
      #[none, ← liftOption a₁.toExpr, ← liftOption a₂.toExpr, ← liftOption a₃.toExpr,
        ← mkDelayedProof h₁, ← mkDelayedProof h₂]
  | .heqOfEq h => mkAppM ``heq_of_eq #[← mkDelayedProof h]
  | .heqSymm h => mkHEqSymm (← mkDelayedProof h)
partial def mkProof (lhs rhs : Expr) (H : EntryExpr) (heqProofs : Bool) : CCM Expr := do
  match H with
  | .congr => mkCongrProof lhs rhs heqProofs
  | .eqTrue =>
    let (flip, some (R, a, b)) ←
      if lhs == .const ``True [] then
        ((true, ·)) <$> rhs.relSidesIfRefl?
      else
        ((false, ·)) <$> lhs.relSidesIfRefl?
      | failure
    let aRb ←
      if R == ``Eq then
        getEqProof a b >>= liftOption
      else if R == ``HEq then
        getHEqProof a b >>= liftOption
      else
        getEqProof a b >>= liftOption >>= fun aEqb => liftM (liftFromEq R aEqb)
    let aRbEqTrue ← mkEqTrue aRb
    if flip then
      mkEqSymm aRbEqTrue
    else
      return aRbEqTrue
  | .refl =>
    let type ← if heqProofs then mkHEq lhs rhs else mkEq lhs rhs
    let proof ← if heqProofs then mkHEqRefl lhs else mkEqRefl lhs
    mkExpectedTypeHint proof type
  | .ofExpr H => return H
  | .ofDExpr H => mkDelayedProof H
partial def getEqProofCore (e₁ e₂ : Expr) (asHEq : Bool) : CCM (Option Expr) := do
  if e₁.hasExprMVar || e₂.hasExprMVar then return none
  if ← pureIsDefEq e₁ e₂ then
    if asHEq then
      return some (← mkHEqRefl e₁)
    else
      return some (← mkEqRefl e₁)
  let some n₁ ← getEntry e₁ | return none
  let some n₂ ← getEntry e₂ | return none
  if n₁.root != n₂.root then return none
  let heqProofs ← hasHEqProofs n₁.root
  let mut path₁ : Array Expr := #[]
  let mut Hs₁ : Array EntryExpr := #[]
  let mut visited : RBExprSet := ∅
  let mut it₁ := e₁
  repeat
    visited := visited.insert it₁
    let some it₁N ← getEntry it₁ | failure
    let some t := it₁N.target | break
    path₁ := path₁.push t
    let some p := it₁N.proof | failure
    Hs₁ := Hs₁.push (← flipProof p it₁N.flipped heqProofs)
    it₁ := t
  guard (it₁ == n₁.root)
  let mut path₂ : Array Expr := #[]
  let mut Hs₂ : Array EntryExpr := #[]
  let mut it₂ := e₂
  repeat
    if visited.contains it₂ then
      break 
    let some it₂N ← getEntry it₂ | failure
    let some t := it₂N.target | failure
    path₂ := path₂.push it₂
    let some p := it₂N.proof | failure
    Hs₂ := Hs₂.push (← flipProof p (!it₂N.flipped) heqProofs)
    it₂ := t
  repeat
    if path₁.isEmpty then
      guard (it₂ == e₁)
      break
    if path₁.back! == it₂ then
      break
    path₁ := path₁.pop
    Hs₁ := Hs₁.pop
  let mut pr? : Option Expr := none
  let mut lhs := e₁
  for i in [:path₁.size] do
    pr? ← some <$> mkTransOpt pr? (← mkProof lhs path₁[i]! Hs₁[i]! heqProofs) heqProofs
    lhs := path₁[i]!
  let mut i := Hs₂.size
  while i > 0 do
    i := i - 1
    pr? ← some <$> mkTransOpt pr? (← mkProof lhs path₂[i]! Hs₂[i]! heqProofs) heqProofs
    lhs := path₂[i]!
  let mut some pr := pr? | failure
  if heqProofs && !asHEq then
    pr ← mkAppM ``eq_of_heq #[pr]
  else if !heqProofs && asHEq then
    pr ← mkAppM ``heq_of_eq #[pr]
  return pr
@[inline]
partial def getEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ false
@[inline]
partial def getHEqProof (e₁ e₂ : Expr) : CCM (Option Expr) :=
  getEqProofCore e₁ e₂ true
end
def getEqTrueProof (e : Expr) : CCM Expr := do
  guard (← isEqTrue e)
  let some p ← getEqProof e (.const ``True []) | failure
  return p
def getEqFalseProof (e : Expr) : CCM Expr := do
  guard (← isEqFalse e)
  let some p ← getEqProof e (.const ``False []) | failure
  return p
def getPropEqProof (a b : Expr) : CCM Expr := do
  guard (← isEqv a b)
  let some p ← getEqProof a b | failure
  return p
def getInconsistencyProof : CCM (Option Expr) := do
  guard !(← get).frozePartitions
  if let some p ← getEqProof (.const ``True []) (.const ``False []) then
    return some (← mkAppM ``false_of_true_eq_false #[p])
  else
    return none
def compareSymmAux (lhs₁ rhs₁ lhs₂ rhs₂ : Expr) : CCM Bool := do
  let lhs₁ ← getRoot lhs₁
  let rhs₁ ← getRoot rhs₁
  let lhs₂ ← getRoot lhs₂
  let rhs₂ ← getRoot rhs₂
  let (lhs₁, rhs₁) := if rhs₁.lt lhs₁ then (rhs₁, lhs₁) else (lhs₁, rhs₁)
  let (lhs₂, rhs₂) := if rhs₂.lt lhs₂ then (rhs₂, lhs₂) else (lhs₂, rhs₂)
  return lhs₁ == lhs₂ && rhs₁ == rhs₂
def compareSymm : (k₁ k₂ : Expr × Name) → CCM Bool
  | (e₁, n₁), (e₂, n₂) => do
    if n₁ != n₂ then return false
    if n₁ == ``Eq || n₁ == ``Iff then
      compareSymmAux e₁.appFn!.appArg! e₁.appArg! e₂.appFn!.appArg! e₂.appArg!
    else
      let some (_, lhs₁, rhs₁) ← e₁.relSidesIfSymm? | failure
      let some (_, lhs₂, rhs₂) ← e₂.relSidesIfSymm? | failure
      compareSymmAux lhs₁ rhs₁ lhs₂ rhs₂
def checkEqTrue (e : Expr) : CCM Unit := do
  let some (_, lhs, rhs) ← e.relSidesIfRefl? | return
  if ← isEqv e (.const ``True []) then return 
  let lhsR ← getRoot lhs
  let rhsR ← getRoot rhs
  if lhsR != rhsR then return
  pushEq e (.const ``True []) .eqTrue
def addCongruenceTable (e : Expr) : CCM Unit := do
  guard e.isApp
  let k ← mkCongruencesKey e
  if let some es := (← get).congruences[k]? then
    for oldE in es do
      if ← isCongruent e oldE then
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := oldE }
        modify fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        let heqProof ← (!·) <$> pureIsDefEq (← inferType e) (← inferType oldE)
        pushTodo e oldE .congr heqProof
        return
    modify fun ccs =>
      { ccs with congruences := ccs.congruences.insert k (e :: es) }
  else
    modify fun ccs =>
      { ccs with congruences := ccs.congruences.insert k [e] }
def addSymmCongruenceTable (e : Expr) : CCM Unit := do
  let some (rel, lhs, rhs) ← e.relSidesIfSymm? | failure
  let k ← mkSymmCongruencesKey lhs rhs
  let newP := (e, rel)
  if let some ps := (← get).symmCongruences[k]? then
    for p in ps do
      if ← compareSymm newP p then
        let some currEntry ← getEntry e | failure
        let newEntry := { currEntry with cgRoot := p.1 }
        modify fun ccs => { ccs with entries := ccs.entries.insert e newEntry }
        if rel == ``Eq || e.getAppNumArgs == 2 then
          pushEq e p.1 .congr
        checkEqTrue e
        return
    modify fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k (newP :: ps) }
    checkEqTrue e
  else
    modify fun ccs =>
      { ccs with symmCongruences := ccs.symmCongruences.insert k [newP] }
    checkEqTrue e
def pushSubsingletonEq (a b : Expr) : CCM Unit := do
  let A ← normalize (← inferType a)
  let B ← normalize (← inferType b)
  if ← pureIsDefEq A B then
    let proof ← mkAppM ``Subsingleton.elim #[a, b]
    pushEq a b proof
  else
    let some AEqB ← getEqProof A B | failure
    let proof ← mkAppM ``Subsingleton.helim #[AEqB, a, b]
    pushHEq a b proof
def checkNewSubsingletonEq (oldRoot newRoot : Expr) : CCM Unit := do
  guard (← isEqv oldRoot newRoot)
  guard ((← getRoot oldRoot) == newRoot)
  let some it₁ := (← get).subsingletonReprs.find? oldRoot | return
  if let some it₂ := (← get).subsingletonReprs.find? newRoot then
    pushSubsingletonEq it₁ it₂
  else
    modify fun ccs =>
      { ccs with subsingletonReprs := ccs.subsingletonReprs.insert newRoot it₁ }
def getEqcLambdas (e : Expr) (r : Array Expr := #[]) : CCM (Array Expr) := do
  guard ((← getRoot e) == e)
  let mut r := r
  let some ee ← getEntry e | failure
  unless ee.hasLambdas do return r
  let mut it := e
  repeat
    if it.isLambda then
      r := r.push it
    let some itN ← getEntry it | failure
    it := itN.next
  until it == e
  return r
def propagateBeta (fn : Expr) (revArgs : Array Expr) (lambdas : Array Expr)
    (newLambdaApps : Array Expr := #[]) : CCM (Array Expr) := do
  let mut newLambdaApps := newLambdaApps
  for lambda in lambdas do
    guard lambda.isLambda
    if fn != lambda then
      if ← pureIsDefEq (← inferType fn) (← inferType lambda) then
        let newApp := mkAppRev lambda revArgs
        newLambdaApps := newLambdaApps.push newApp
  return newLambdaApps
def mkNeOfEqOfNe (a a₁ a₁NeB : Expr) : CCM (Option Expr) := do
  guard (← isEqv a a₁)
  if a == a₁ then
    return some a₁NeB
  let aEqA₁ ← getEqProof a a₁
  match aEqA₁ with
  | none => return none 
  | some aEqA₁ => mkAppM ``ne_of_eq_of_ne #[aEqA₁, a₁NeB]
def mkNeOfNeOfEq (aNeB₁ b₁ b : Expr) : CCM (Option Expr) := do
  guard (← isEqv b b₁)
  if b == b₁ then
    return some aNeB₁
  let b₁EqB ← getEqProof b b₁
  match b₁EqB with
  | none => return none 
  | some b₁EqB => mkAppM ``ne_of_ne_of_eq #[aNeB₁, b₁EqB]
def isAC (e : Expr) : CCM (Option Expr) := do
  let .app (.app op _) _ := e | return none
  let ccs ← get
  if let some cop := ccs.canOps.find? op then
    let some b := ccs.opInfo.find? cop
      | throwError "opInfo should contain all canonical operators in canOps"
    return bif b then some cop else none
  for (cop, b) in ccs.opInfo do
    if ← pureIsDefEq op cop then
      modify fun _ => { ccs with canOps := ccs.canOps.insert op cop }
      return bif b then some cop else none
  let b ←
    try
      let aop ← mkAppM ``Std.Associative #[op]
      let some _ ← synthInstance? aop | failure
      let cop ← mkAppM ``Std.Commutative #[op]
      let some _ ← synthInstance? cop | failure
      pure true
    catch _ =>
      pure false
  modify fun _ =>
    { ccs with
      canOps := ccs.canOps.insert op op
      opInfo := ccs.opInfo.insert op b }
  return bif b then some op else none
open MessageData in
def dbgTraceACEq (header : String) (lhs rhs : ACApps) : CCM Unit := do
  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac]
    group (ofFormat (header ++ .line) ++ ccs.ppACApps lhs ++
      ofFormat (.line ++ "=" ++ .line) ++ ccs.ppACApps rhs)
open MessageData in
def dbgTraceACState : CCM Unit := do
  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac] group ("state: " ++ nest 6 ccs.ppAC)
def mkACProof (e₁ e₂ : Expr) : MetaM Expr := do
  let eq ← mkEq e₁ e₂
  let .mvar m ← mkFreshExprSyntheticOpaqueMVar eq | failure
  AC.rewriteUnnormalizedRefl m
  let pr ← instantiateMVars (.mvar m)
  mkExpectedTypeHint pr eq
def mkACSimpProof (tr t s r sr : ACApps) (tEqs : DelayedExpr) : MetaM DelayedExpr := do
  if tr == t then
    return tEqs
  else if tr == sr then
    let some tre := tr.toExpr | failure
    DelayedExpr.ofExpr <$> mkEqRefl tre
  else
    let .apps op _ := tr | failure
    let some re := r.toExpr | failure
    let some te := t.toExpr | failure
    let some se := s.toExpr | failure
    let some tre := tr.toExpr | failure
    let some sre := sr.toExpr | failure
    let opr := op.app re 
    let rt := mkApp2 op re te 
    let rs := mkApp2 op re se 
    let rtEqrs := DelayedExpr.congrArg opr tEqs
    let trEqrt ← mkACProof tre rt
    let rsEqsr ← mkACProof rs sre
    return .eqTrans (.eqTrans trEqrt rtEqrs) rsEqsr
def mkACSuperposeProof (ra sb a b r s ts tr : ACApps) (tsEqa trEqb : DelayedExpr) :
    MetaM DelayedExpr := do
  let .apps _ _ := tr | failure
  let .apps op _ := ts | failure
  let some tse := ts.toExpr | failure
  let some re := r.toExpr | failure
  let some tre := tr.toExpr | failure
  let some se := s.toExpr | failure
  let some ae := a.toExpr | failure
  let some be := b.toExpr | failure
  let some rae := ra.toExpr | failure
  let some sbe := sb.toExpr | failure
  let tsrEqar := DelayedExpr.congrFun (.congrArg op tsEqa) r 
  let trsEqbs := DelayedExpr.congrFun (.congrArg op trEqb) s 
  let tsr := mkApp2 op tse re 
  let trs := mkApp2 op tre se 
  let ar := mkApp2 op ae re 
  let bs := mkApp2 op be se 
  let tsrEqtrs ← mkACProof tsr trs 
  let raEqar ← mkACProof rae ar 
  let bsEqsb ← mkACProof bs sbe 
  return .eqTrans raEqar (.eqTrans (.eqSymm tsrEqar) (.eqTrans tsrEqtrs (.eqTrans trsEqbs bsEqsb)))
def simplifyACCore (e lhs rhs : ACApps) (H : DelayedExpr) :
    CCM (ACApps × DelayedExpr) := do
  guard (lhs.isSubset e)
  if e == lhs then
    return (rhs, H)
  else
    let .apps op _ := e | failure
    let newArgs := e.diff lhs
    let r : ACApps := if newArgs.isEmpty then default else .mkApps op newArgs
    let newArgs := ACApps.append op rhs newArgs
    let newE := ACApps.mkApps op newArgs
    let some true := (← get).opInfo.find? op | failure
    let newPr ← mkACSimpProof e lhs rhs r newE H
    return (newE, newPr)
def simplifyACStep (e : ACApps) : CCM (Option (ACApps × DelayedExpr)) := do
  if let .apps _ args := e then
    for h : i in [:args.size] do
      if i == 0 || (args[i]'h.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) h.2)) then
        let some ae := (← get).acEntries.find? (args[i]'h.2) | failure
        let occs := ae.RLHSOccs
        let mut Rlhs? : Option ACApps := none
        for Rlhs in occs do
          if Rlhs.isSubset e then
            Rlhs? := some Rlhs
            break
        if let some Rlhs := Rlhs? then
          let some (Rrhs, H) := (← get).acR.find? Rlhs | failure
          return (some <| ← simplifyACCore e Rlhs Rrhs H)
  else if let some p := (← get).acR.find? e then
    return some p
  return none
def simplifyAC (e : ACApps) : CCM (Option (ACApps × DelayedExpr)) := do
  let mut some (curr, pr) ← simplifyACStep e | return none
  repeat
    let some (newCurr, newPr) ← simplifyACStep curr | break
    pr := .eqTransOpt e curr newCurr pr newPr
    curr := newCurr
  return some (curr, pr)
def insertEraseROcc (arg : Expr) (lhs : ACApps) (inLHS isInsert : Bool) : CCM Unit := do
  let some entry := (← get).acEntries.find? arg | failure
  let occs := entry.ROccs inLHS
  let newOccs := if isInsert then occs.insert lhs else occs.erase (compare lhs)
  let newEntry :=
    if inLHS then { entry with RLHSOccs := newOccs } else { entry with RRHSOccs := newOccs }
  modify fun ccs => { ccs with acEntries := ccs.acEntries.insert arg newEntry }
def insertEraseROccs (e lhs : ACApps) (inLHS isInsert : Bool) : CCM Unit := do
  match e with
  | .apps _ args =>
    insertEraseROcc args[0]! lhs inLHS isInsert
    for i in [1:args.size] do
      if args[i]! != args[i - 1]! then
        insertEraseROcc args[i]! lhs inLHS isInsert
  | .ofExpr e => insertEraseROcc e lhs inLHS isInsert
@[inline]
def insertROccs (e lhs : ACApps) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS true
@[inline]
def eraseROccs (e lhs : ACApps) (inLHS : Bool) : CCM Unit :=
  insertEraseROccs e lhs inLHS false
@[inline]
def insertRBHSOccs (lhs rhs : ACApps) : CCM Unit := do
  insertROccs lhs lhs true
  insertROccs rhs lhs false
@[inline]
def eraseRBHSOccs (lhs rhs : ACApps) : CCM Unit := do
  eraseROccs lhs lhs true
  eraseROccs rhs lhs false
@[inline]
def insertRRHSOccs (e lhs : ACApps) : CCM Unit :=
  insertROccs e lhs false
@[inline]
def eraseRRHSOccs (e lhs : ACApps) : CCM Unit :=
  eraseROccs e lhs false
open MessageData in
def composeAC (lhs rhs : ACApps) (H : DelayedExpr) : CCM Unit := do
  let some x := (← get).getVarWithLeastRHSOccs lhs | failure
  let some ent := (← get).acEntries.find? x | failure
  let occs := ent.RRHSOccs
  for Rlhs in occs do
    let some (Rrhs, RH) := (← get).acR.find? Rlhs | failure
    if lhs.isSubset Rrhs then
      let (newRrhs, RrhsEqNewRrhs) ← simplifyACCore Rrhs lhs rhs H
      let newRH := DelayedExpr.eqTransOpt Rlhs Rrhs newRrhs RH RrhsEqNewRrhs
      modify fun ccs => { ccs with acR := ccs.acR.insert Rlhs (newRrhs, newRH) }
      eraseRRHSOccs Rrhs Rlhs
      insertRRHSOccs newRrhs Rlhs
      let ccs ← get
      trace[Debug.Meta.Tactic.cc.ac] group <|
        let oldRw :=
          paren (ccs.ppACApps Rlhs ++ ofFormat (Format.line ++ "
        let newRw :=
          paren (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "
        "compose: " ++ nest 9 (group
          (oldRw ++ ofFormat (Format.line ++ "with" ++ .line) ++ newRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApps newRrhs)
open MessageData in
def collapseAC (lhs rhs : ACApps) (H : DelayedExpr) : CCM Unit := do
  let some x := (← get).getVarWithLeastLHSOccs lhs | failure
  let some ent := (← get).acEntries.find? x | failure
  let occs := ent.RLHSOccs
  for Rlhs in occs do
    if lhs.isSubset Rlhs then
      let some (Rrhs, RH) := (← get).acR.find? Rlhs | failure
      eraseRBHSOccs Rlhs Rrhs
      modify fun ccs => { ccs with acR := ccs.acR.erase Rlhs }
      let (newRlhs, RlhsEqNewRlhs) ← simplifyACCore Rlhs lhs rhs H
      let newRlhsEqRlhs := DelayedExpr.eqSymmOpt Rlhs newRlhs RlhsEqNewRlhs
      let newRH := DelayedExpr.eqTransOpt newRlhs Rlhs Rrhs newRlhsEqRlhs RH
      modifyACTodo fun todo => todo.push (newRlhs, Rrhs, newRH)
      let ccs ← get
      trace[Debug.Meta.Tactic.cc.ac] group <|
        let newRw :=
          paren (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "
        let oldRw :=
          paren (ccs.ppACApps Rrhs ++ ofFormat (Format.line ++ "<
        "collapse: " ++ nest 10 (group
          (newRw ++ ofFormat (Format.line ++ "at" ++ .line) ++ oldRw) ++
            ofFormat (Format.line ++ ":=" ++ .line) ++ ccs.ppACApps newRlhs)
open MessageData in
def superposeAC (ts a : ACApps) (tsEqa : DelayedExpr) : CCM Unit := do
  let .apps op args := ts | return
  for hi : i in [:args.size] do
    if i == 0 || (args[i]'hi.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2)) then
      let some ent := (← get).acEntries.find? (args[i]'hi.2) | failure
      let occs := ent.RLHSOccs
      for tr in occs do
        let .apps optr _ := tr | continue
        unless optr == op do continue
        let some (b, trEqb) := (← get).acR.find? tr | failure
        let tArgs := ts.intersection tr
        guard !tArgs.isEmpty
        let t := ACApps.mkApps op tArgs
        let sArgs := ts.diff t
        guard !sArgs.isEmpty
        let rArgs := tr.diff t
        guard !rArgs.isEmpty
        let s := ACApps.mkApps op sArgs
        let r := ACApps.mkApps op rArgs
        let ra := ACApps.mkFlatApps op r a
        let sb := ACApps.mkFlatApps op s b
        let some true := (← get).opInfo.find? op | failure
        let raEqsb ← mkACSuperposeProof ra sb a b r s ts tr tsEqa trEqb
        modifyACTodo fun todo => todo.push (ra, sb, raEqsb)
        let ccs ← get
        trace[Debug.Meta.Tactic.cc.ac] group <|
          let rw₁ :=
            paren (ccs.ppACApps ts ++ ofFormat (Format.line ++ "
          let rw₂ :=
            paren (ccs.ppACApps tr ++ ofFormat (Format.line ++ "
          let eq :=
            paren (ccs.ppACApps ra ++ ofFormat (Format.line ++ "
          "superpose: " ++ nest 11 (group
            (rw₁ ++ ofFormat (Format.line ++ "with" ++ .line) ++ rw₂) ++
              ofFormat (Format.line ++ ":=" ++ .line) ++ eq)
open MessageData in
def processAC : CCM Unit := do
  repeat
    let acTodo ← getACTodo
    let mut some (lhs, rhs, H) := acTodo.back? | break
    modifyACTodo fun _ => acTodo.pop
    let lhs₀ := lhs
    let rhs₀ := rhs
    dbgTraceACEq "process eq:" lhs rhs
    if let some p ← simplifyAC lhs then
      H := .eqTransOpt p.1 lhs rhs (.eqSymmOpt lhs p.1 p.2) H
      lhs := p.1
    if let some p ← simplifyAC rhs then
      H := .eqTransOpt lhs rhs p.1 H p.2
      rhs := p.1
    if lhs != lhs₀ || rhs != rhs₀ then
      dbgTraceACEq "after simp:" lhs rhs
    if lhs == rhs then
      trace[Debug.Meta.Tactic.cc.ac] "trivial"
      continue
    if let .ofExpr lhse := lhs then
      if let .ofExpr rhse := rhs then
        if (← getRoot lhse) != (← getRoot rhse) then
          pushEq lhse rhse (.ofDExpr H)
    if compare lhs rhs == .lt then
      H := .eqSymmOpt lhs rhs H
      (lhs, rhs) := (rhs, lhs)
    composeAC lhs rhs H
    collapseAC lhs rhs H
    superposeAC lhs rhs H
    modify fun ccs => { ccs with acR := ccs.acR.insert lhs (rhs, H) }
    insertRBHSOccs lhs rhs
    let ccs ← get
    trace[Debug.Meta.Tactic.cc.ac] group <|
      "new rw: " ++
        group (ccs.ppACApps lhs ++ ofFormat (Format.line ++ "
def addACEq (e₁ e₂ : Expr) : CCM Unit := do
  dbgTraceACEq "cc eq:" e₁ e₂
  modifyACTodo fun acTodo => acTodo.push (e₁, e₂, .eqProof e₁ e₂)
  processAC
  dbgTraceACState
def setACVar (e : Expr) : CCM Unit := do
  let eRoot ← getRoot e
  let some rootEntry ← getEntry eRoot | failure
  if let some acVar := rootEntry.acVar then
    addACEq acVar e
  else
    let newRootEntry := { rootEntry with acVar := some e }
    modify fun ccs => { ccs with entries := ccs.entries.insert eRoot newRootEntry }
def internalizeACVar (e : Expr) : CCM Bool := do
  let ccs ← get
  if ccs.acEntries.contains e then return false
  modify fun _ =>
    { ccs with
      acEntries := ccs.acEntries.insert e { idx := ccs.acEntries.size } }
  setACVar e
  return true
partial def convertAC (op e : Expr) (args : Array Expr := #[]) : CCM (Array Expr × Expr) := do
  if let some currOp ← isAC e then
    if op == currOp then
      let (args, arg₁) ← convertAC op e.appFn!.appArg! args
      let (args, arg₂) ← convertAC op e.appArg! args
      return (args, mkApp2 op arg₁ arg₂)
  let _ ← internalizeACVar e
  return (args.push e, e)
open MessageData in
def internalizeAC (e : Expr) (parent? : Option Expr) : CCM Unit := do
  let some op ← isAC e | return
  let parentOp? ← parent?.casesOn (pure none) isAC
  if parentOp?.any (· == op) then return
  unless (← internalizeACVar e) do return
  let (args, norme) ← convertAC op e
  let rep := ACApps.mkApps op args
  let some true := (← get).opInfo.find? op | failure
  let some repe := rep.toExpr | failure
  let pr ← mkACProof norme repe
  let ccs ← get
  trace[Debug.Meta.Tactic.cc.ac] group <|
    let d := paren (ccs.ppACApps e ++ ofFormat (" :=" ++ Format.line) ++ ofExpr e)
    "new term: " ++ d ++ ofFormat (Format.line ++ "===>" ++ .line) ++ ccs.ppACApps rep
  modifyACTodo fun todo => todo.push (e, rep, pr)
  processAC
  dbgTraceACState
mutual
partial def internalizeAppLit (e : Expr) : CCM Unit := do
  if ← isInterpretedValue e then
    mkEntry e true
    if (← get).values then return 
  else
    mkEntry e false
    if (← get).values && isValue e then return 
  unless e.isApp do return
  if let some (_, lhs, rhs) ← e.relSidesIfSymm? then
    internalizeCore lhs (some e)
    internalizeCore rhs (some e)
    addOccurrence e lhs true
    addOccurrence e rhs true
    addSymmCongruenceTable e
  else if (← mkCCCongrTheorem e).isSome then
    let fn := e.getAppFn
    let apps := e.getAppApps
    guard (apps.size > 0)
    guard (apps.back! == e)
    let mut pinfo : List ParamInfo := []
    let state ← get
    if state.ignoreInstances then
      pinfo := (← getFunInfoNArgs fn apps.size).paramInfo.toList
    if state.hoFns.isSome && fn.isConst && !(state.hoFns.iget.contains fn.constName) then
      for h : i in [:apps.size] do
        let arg := (apps[i]'h.2).appArg!
        addOccurrence e arg false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          mkEntry arg false
          propagateInstImplicit arg
        else
          internalizeCore arg (some e)
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
      internalizeCore fn (some e)
      addOccurrence e fn false
      setFO e
      addCongruenceTable e
    else
      for h : i in [:apps.size] do
        let curr := apps[i]'h.2
        let .app currFn currArg := curr | unreachable!
        if i < apps.size - 1 then
          mkEntry curr false
        for h : j in [i:apps.size] do
          addOccurrence (apps[j]'h.2) currArg false
          addOccurrence (apps[j]'h.2) currFn false
        if pinfo.head?.any ParamInfo.isInstImplicit then
          mkEntry currArg false
          mkEntry currFn false
          propagateInstImplicit currArg
        else
          internalizeCore currArg (some e)
          mkEntry currFn false
        unless pinfo.isEmpty do
          pinfo := pinfo.tail
        addCongruenceTable curr
  applySimpleEqvs e
partial def internalizeCore (e : Expr) (parent? : Option Expr) : CCM Unit := do
  guard !e.hasLooseBVars
  if e.hasExprMVar && !(← get).frozePartitions then
    return
  if (← getEntry e).isNone then
    match e with
    | .bvar _ => unreachable!
    | .sort _ => pure ()
    | .const _ _ | .mvar _ => mkEntry e false
    | .lam _ _ _ _ | .letE _ _ _ _ _ => mkEntry e false
    | .fvar f =>
      mkEntry e false
      if let some v ← f.getValue? then
        pushReflEq e v
    | .mdata _ e' =>
      mkEntry e false
      internalizeCore e' e
      addOccurrence e e' false
      pushReflEq e e'
    | .forallE _ t b _ =>
      if e.isArrow then
        if ← isProp t <&&> isProp b then
          internalizeCore t e
          internalizeCore b e
          addOccurrence e t false
          addOccurrence e b false
          propagateImpUp e
      if ← isProp e then
        mkEntry e false
    | .app _ _ | .lit _ => internalizeAppLit e
    | .proj sn i pe =>
      mkEntry e false
      let some fn := (getStructureFields (← getEnv) sn)[i]? | failure
      let e' ← pe.mkDirectProjection fn
      internalizeAppLit e'
      pushReflEq e e'
  if (← get).ac then
    internalizeAC e parent?
partial def propagateIffUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.iff? | failure
  if ← isEqTrue a then
    pushEq e b (mkApp3 (.const ``iff_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    pushEq e a (mkApp3 (.const ``iff_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqv a b then
    pushEq e (.const ``True []) (mkApp3 (.const ``iff_eq_true_of_eq []) a b (← getPropEqProof a b))
partial def propagateAndUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.and? | failure
  if ← isEqTrue a then
    pushEq e b (mkApp3 (.const ``and_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    pushEq e a (mkApp3 (.const ``and_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse a then
    pushEq e (.const ``False [])
      (mkApp3 (.const ``and_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqFalse b then
    pushEq e (.const ``False [])
      (mkApp3 (.const ``and_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    pushEq e a (mkApp3 (.const ``and_eq_of_eq []) a b (← getPropEqProof a b))
partial def propagateOrUp (e : Expr) : CCM Unit := do
  let some (a, b) := e.app2? ``Or | failure
  if ← isEqTrue a then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``or_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqTrue b then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``or_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse a then
    pushEq e b (mkApp3 (.const ``or_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqFalse b then
    pushEq e a (mkApp3 (.const ``or_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    pushEq e a (mkApp3 (.const ``or_eq_of_eq []) a b (← getPropEqProof a b))
partial def propagateNotUp (e : Expr) : CCM Unit := do
  let some a := e.not? | failure
  if ← isEqTrue a then
    pushEq e (.const ``False []) (mkApp2 (.const ``not_eq_of_eq_true []) a (← getEqTrueProof a))
  else if ← isEqFalse a then
    pushEq e (.const ``True []) (mkApp2 (.const ``not_eq_of_eq_false []) a (← getEqFalseProof a))
  else if ← isEqv a e then
    let falsePr := mkApp2 (.const ``false_of_a_eq_not_a []) a (← getPropEqProof a e)
    let H := Expr.app (.const ``true_eq_false_of_false []) falsePr
    pushEq (.const ``True []) (.const ``False []) H
partial def propagateImpUp (e : Expr) : CCM Unit := do
  guard e.isArrow
  let .forallE _ a b _ := e | unreachable!
  if ← isEqTrue a then
    pushEq e b (mkApp3 (.const ``imp_eq_of_eq_true_left []) a b (← getEqTrueProof a))
  else if ← isEqFalse a then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_of_eq_false_left []) a b (← getEqFalseProof a))
  else if ← isEqTrue b then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_of_eq_true_right []) a b (← getEqTrueProof b))
  else if ← isEqFalse b then
    let isNot : Expr → Bool × Expr
      | .app (.const ``Not []) a => (true, a)
      | .forallE _ a (.const ``False []) _ => (true, a)
      | e => (false, e)
    if let (true, arg) := isNot a then
      if (← get).em then
        pushEq e arg
          (mkApp3 (.const ``not_imp_eq_of_eq_false_right []) arg b (← getEqFalseProof b))
    else
      let notA := mkApp (.const ``Not []) a
      internalizeCore notA none
      pushEq e notA
        (mkApp3 (.const ``imp_eq_of_eq_false_right []) a b (← getEqFalseProof b))
  else if ← isEqv a b then
    pushEq e (.const ``True [])
      (mkApp3 (.const ``imp_eq_true_of_eq []) a b (← getPropEqProof a b))
partial def propagateIteUp (e : Expr) : CCM Unit := do
  let .app (.app (.app (.app (.app (.const ``ite [lvl]) A) c) d) a) b := e | failure
  if ← isEqTrue c then
    pushEq e a (mkApp6 (.const ``if_eq_of_eq_true [lvl]) c d A a b (← getEqTrueProof c))
  else if ← isEqFalse c then
    pushEq e b (mkApp6 (.const ``if_eq_of_eq_false [lvl]) c d A a b (← getEqFalseProof c))
  else if ← isEqv a b then
    pushEq e a (mkApp6 (.const ``if_eq_of_eq [lvl]) c d A a b (← getPropEqProof a b))
partial def propagateEqUp (e : Expr) : CCM Unit := do
  let some (_, a, b) := e.eq? | failure
  let ra ← getRoot a
  let rb ← getRoot b
  if ra != rb then
    let mut raNeRb : Option Expr := none
    if ← isInterpretedValue ra <&&> isInterpretedValue rb <&&>
        pure (ra.int?.isNone || ra.int? != rb.int?) then
      raNeRb := some
        (Expr.app (.proj ``Iff 0 (← mkAppOptM ``bne_iff_ne #[none, none, none, ra, rb]))
          (← mkEqRefl (.const ``true [])))
    else
      if let some c₁ ← isConstructorApp? ra then
      if let some c₂ ← isConstructorApp? rb then
      if c₁.name != c₂.name then
        raNeRb ← withLocalDeclD `h (← mkEq ra rb) fun h => do
          mkLambdaFVars #[h] (← mkNoConfusion (.const ``False []) h)
    if let some raNeRb' := raNeRb then
    if let some aNeRb ← mkNeOfEqOfNe a ra raNeRb' then
    if let some aNeB ← mkNeOfNeOfEq aNeRb rb b then
      pushEq e (.const ``False []) (← mkEqFalse aNeB)
partial def propagateUp (e : Expr) : CCM Unit := do
  if (← get).inconsistent then return
  if e.isAppOfArity ``Iff 2 then
    propagateIffUp e
  else if e.isAppOfArity ``And 2 then
    propagateAndUp e
  else if e.isAppOfArity ``Or 2 then
    propagateOrUp e
  else if e.isAppOfArity ``Not 1 then
    propagateNotUp e
  else if e.isArrow then
    propagateImpUp e
  else if e.isIte then
    propagateIteUp e
  else if e.isEq then
    propagateEqUp e
partial def applySimpleEqvs (e : Expr) : CCM Unit := do
  if let .app (.app (.app (.app (.const ``cast [l₁]) A) B) H) a := e then
    let proof := mkApp4 (.const ``cast_heq [l₁]) A B H a
    pushHEq e a proof
  if let .app (.app (.app (.app (.app (.app (.const ``Eq.rec [l₁, l₂]) A) a) P) p) a') H := e then
    let proof := mkApp6 (.const ``eqRec_heq' [l₁, l₂]) A a P p a' H
    pushHEq e p proof
  if let .app (.app (.app (.const ``Ne [l₁]) α) a) b := e then
    let newE := Expr.app (.const ``Not []) (mkApp3 (.const ``Eq [l₁]) α a b)
    internalizeCore newE none
    pushReflEq e newE
  if let some r ← e.reduceProjStruct? then
    pushReflEq e r
  let fn := e.getAppFn
  if fn.isLambda then
    let reducedE := e.headBeta
    if let some phandler := (← get).phandler then
      phandler.newAuxCCTerm reducedE
    internalizeCore reducedE none
    pushReflEq e reducedE
  let mut revArgs : Array Expr := #[]
  let mut it := e
  while it.isApp do
    revArgs := revArgs.push it.appArg!
    let fn := it.appFn!
    let rootFn ← getRoot fn
    let en ← getEntry rootFn
    if en.any Entry.hasLambdas then
      let lambdas ← getEqcLambdas rootFn
      let newLambdaApps ← propagateBeta fn revArgs lambdas
      for newApp in newLambdaApps do
        internalizeCore newApp none
    it := fn
  propagateUp e
partial def processSubsingletonElem (e : Expr) : CCM Unit := do
  let type ← inferType e
  let ss ← synthInstance? (← mkAppM ``Subsingleton #[type])
  if ss.isNone then return 
  let type ← normalize type
  internalizeCore type none
  if let some it := (← get).subsingletonReprs.find? type then
    pushSubsingletonEq e it
  else
    modify fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert type e }
  let typeRoot ← getRoot type
  if typeRoot == type then return
  if let some it2 := (← get).subsingletonReprs.find? typeRoot then
    pushSubsingletonEq e it2
  else
    modify fun ccs =>
      { ccs with
        subsingletonReprs := ccs.subsingletonReprs.insert typeRoot e }
partial def mkEntry (e : Expr) (interpreted : Bool) : CCM Unit := do
  if (← getEntry e).isSome then return
  let constructor ← isConstructorApp e
  modify fun ccs =>
    { ccs with toCCState := ccs.toCCState.mkEntryCore e interpreted constructor }
  processSubsingletonElem e
end
def mayPropagate (e : Expr) : Bool :=
  e.isAppOfArity ``Iff 2 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 ||
    e.isAppOfArity ``Not 1 || e.isArrow || e.isIte
def removeParents (e : Expr) (parentsToPropagate : Array Expr := #[]) : CCM (Array Expr) := do
  let some ps := (← get).parents.find? e | return parentsToPropagate
  let mut parentsToPropagate := parentsToPropagate
  for pocc in ps do
    let p := pocc.expr
    trace[Debug.Meta.Tactic.cc] "remove parent: {p}"
    if mayPropagate p then
      parentsToPropagate := parentsToPropagate.push p
    if p.isApp then
      if pocc.symmTable then
        let some (rel, lhs, rhs) ← p.relSidesIfSymm? | failure
        let k' ← mkSymmCongruencesKey lhs rhs
        if let some lst := (← get).symmCongruences[k']? then
          let k := (p, rel)
          let newLst ← lst.filterM fun k₂ => (!·) <$> compareSymm k k₂
          if !newLst.isEmpty then
            modify fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.insert k' newLst }
          else
            modify fun ccs =>
              { ccs with symmCongruences := ccs.symmCongruences.erase k' }
      else
        let k' ← mkCongruencesKey p
        if let some es := (← get).congruences[k']? then
          let newEs := es.erase p
          if !newEs.isEmpty then
            modify fun ccs =>
              { ccs with congruences := ccs.congruences.insert k' newEs }
          else
            modify fun ccs =>
              { ccs with congruences := ccs.congruences.erase k' }
  return parentsToPropagate
partial def invertTrans (e : Expr) (newFlipped : Bool := false) (newTarget : Option Expr := none)
    (newProof : Option EntryExpr := none) : CCM Unit := do
  let some n ← getEntry e | failure
  if let some t := n.target then
    invertTrans t (!n.flipped) (some e) n.proof
  let newN : Entry :=
    { n with
      flipped := newFlipped
      target := newTarget
      proof := newProof }
  modify fun ccs => { ccs with entries := ccs.entries.insert e newN }
def collectFnRoots (root : Expr) (fnRoots : Array Expr := #[]) : CCM (Array Expr) := do
  guard ((← getRoot root) == root)
  let mut fnRoots : Array Expr := fnRoots
  let mut visited : RBExprSet := ∅
  let mut it := root
  repeat
    let fnRoot ← getRoot (it.getAppFn)
    if !visited.contains fnRoot then
      visited := visited.insert fnRoot
      fnRoots := fnRoots.push fnRoot
    let some itN ← getEntry it | failure
    it := itN.next
  until it == root
  return fnRoots
def reinsertParents (e : Expr) : CCM Unit := do
  let some ps := (← get).parents.find? e | return
  for p in ps do
    trace[Debug.Meta.Tactic.cc] "reinsert parent: {p.expr}"
    if p.expr.isApp then
      if p.symmTable then
        addSymmCongruenceTable p.expr
      else
        addCongruenceTable p.expr
def checkInvariant : CCM Unit := do
  guard (← get).checkInvariant
def propagateBetaToEqc (fnRoots lambdas : Array Expr) (newLambdaApps : Array Expr := #[]) :
    CCM (Array Expr) := do
  if lambdas.isEmpty then return newLambdaApps
  let mut newLambdaApps := newLambdaApps
  let lambdaRoot ← getRoot lambdas.back!
  guard (← lambdas.allM fun l => pure l.isLambda <&&> (· == lambdaRoot) <$> getRoot l)
  for fnRoot in fnRoots do
    if let some ps := (← get).parents.find? fnRoot then
      for { expr := p,.. } in ps do
        let mut revArgs : Array Expr := #[]
        let mut it₂ := p
        while it₂.isApp do
          let fn := it₂.appFn!
          revArgs := revArgs.push it₂.appArg!
          if (← getRoot fn) == lambdaRoot then
            newLambdaApps ← propagateBeta fn revArgs lambdas newLambdaApps
            break
          it₂ := it₂.appFn!
  return newLambdaApps
def propagateProjectionConstructor (p c : Expr) : CCM Unit := do
  guard (← isConstructorApp c)
  p.withApp fun pFn pArgs => do
    let some pFnN := pFn.constName? | return
    let some info ← getProjectionFnInfo? pFnN | return
    let mkidx := info.numParams
    if h : mkidx < pArgs.size then
      unless ← isEqv (pArgs[mkidx]'h) c do return
      unless ← pureIsDefEq (← inferType (pArgs[mkidx]'h)) (← inferType c) do return
      let pArgs := pArgs.set mkidx c
      let newP := mkAppN pFn pArgs
      internalizeCore newP none
    else
      return
partial def propagateConstructorEq (e₁ e₂ : Expr) : CCM Unit := do
  let env ← getEnv
  let some c₁ ← isConstructorApp? e₁ | failure
  let some c₂ ← isConstructorApp? e₂ | failure
  unless ← pureIsDefEq (← inferType e₁) (← inferType e₂) do
    return
  let some h ← getEqProof e₁ e₂ | failure
  if c₁.name == c₂.name then
    if 0 < c₁.numFields then
      let name := mkInjectiveTheoremNameFor c₁.name
      if env.contains name then
        let rec
          go (type val : Expr) : CCM Unit := do
            let push (type val : Expr) : CCM Unit :=
              match type.eq? with
              | some (_, lhs, rhs) => pushEq lhs rhs val
              | none =>
                match type.heq? with
                | some (_, _, lhs, rhs) => pushHEq lhs rhs val
                | none => failure
            match type.and? with
            | some (l, r) =>
              push l (.proj ``And 0 val)
              go r (.proj ``And 1 val)
            | none =>
              push type val
        let val ← mkAppM name #[h]
        let type ← inferType val
        go type val
  else
    let falsePr ← mkNoConfusion (.const ``False []) h
    let H := Expr.app (.const ``true_eq_false_of_false []) falsePr
    pushEq (.const ``True []) (.const ``False []) H
def propagateValueInconsistency (e₁ e₂ : Expr) : CCM Unit := do
  guard (← isInterpretedValue e₁)
  guard (← isInterpretedValue e₂)
  let some eqProof ← getEqProof e₁ e₂ | failure
  let trueEqFalse ← mkEq (.const ``True []) (.const ``False [])
  let neProof :=
    Expr.app (.proj ``Iff 0 (← mkAppOptM ``bne_iff_ne #[none, none, none, e₁, e₂]))
      (← mkEqRefl (.const ``true []))
  let H ← mkAbsurd trueEqFalse eqProof neProof
  pushEq (.const ``True []) (.const ``False []) H
def propagateAndDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.and? | failure
    let h ← getEqTrueProof e
    pushEq a (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_left []) a b h)
    pushEq b (.const ``True []) (mkApp3 (.const ``eq_true_of_and_eq_true_right []) a b h)
def propagateOrDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let some (a, b) := e.app2? ``Or | failure
    let h ← getEqFalseProof e
    pushEq a (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_left []) a b h)
    pushEq b (.const ``False []) (mkApp3 (.const ``eq_false_of_or_eq_false_right []) a b h)
def propagateNotDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some a := e.not? | failure
    pushEq a (.const ``False [])
      (mkApp2 (.const ``eq_false_of_not_eq_true []) a (← getEqTrueProof e))
  else if ← (·.em) <$> get <&&> isEqFalse e then
    let some a := e.not? | failure
    pushEq a (.const ``True [])
      (mkApp2 (.const ``eq_true_of_not_eq_false []) a (← getEqFalseProof e))
def propagateEqDown (e : Expr) : CCM Unit := do
  if ← isEqTrue e then
    let some (a, b) := e.eqOrIff? | failure
    pushEq a b (← mkAppM ``of_eq_true #[← getEqTrueProof e])
def propagateExistsDown (e : Expr) : CCM Unit := do
  if ← isEqFalse e then
    let hNotE ← mkAppM ``of_eq_false #[← getEqFalseProof e]
    let (all, hAll) ← e.forallNot_of_notExists hNotE
    internalizeCore all none
    pushEq all (.const ``True []) (← mkEqTrue hAll)
def propagateDown (e : Expr) : CCM Unit := do
  if e.isAppOfArity ``And 2 then
    propagateAndDown e
  else if e.isAppOfArity ``Or 2 then
    propagateOrDown e
  else if e.isAppOfArity ``Not 1 then
    propagateNotDown e
  else if e.isEq || e.isAppOfArity ``Iff 2 then
    propagateEqDown e
  else if e.isAppOfArity ``Exists 2 then
    propagateExistsDown e
def addEqvStep (e₁ e₂ : Expr) (H : EntryExpr) (heqProof : Bool) : CCM Unit := do
  let some n₁ ← getEntry e₁ | return 
  let some n₂ ← getEntry e₂ | return 
  if n₁.root == n₂.root then return 
  let some r₁ ← getEntry n₁.root | failure
  let some r₂ ← getEntry n₂.root | failure
  if (r₁.interpreted && !r₂.interpreted) ||
      (r₁.constructor && !r₂.interpreted && !r₂.constructor) ||
      (decide (r₁.size > r₂.size) && !r₂.interpreted && !r₂.constructor) then
    go e₂ e₁ n₂ n₁ r₂ r₁ true H heqProof
  else
    go e₁ e₂ n₁ n₂ r₁ r₂ false H heqProof
where
  go (e₁ e₂: Expr) (n₁ n₂ r₁ r₂ : Entry) (flipped : Bool) (H : EntryExpr) (heqProof : Bool) :
      CCM Unit := do
    let mut valueInconsistency := false
    if r₁.interpreted && r₂.interpreted then
      if n₁.root.isConstOf ``True || n₂.root.isConstOf ``True then
        modify fun ccs => { ccs with inconsistent := true }
      else if n₁.root.int?.isSome && n₂.root.int?.isSome then
        valueInconsistency := n₁.root.int? != n₂.root.int?
      else
        valueInconsistency := true
    let e₁Root := n₁.root
    let e₂Root := n₂.root
    trace[Debug.Meta.Tactic.cc] "merging\n{e₁} ==> {e₁Root}\nwith\n{e₂Root} <== {e₂}"
    invertTrans e₁
    let newN₁ : Entry :=
      { n₁ with
        target := e₂
        proof := H
        flipped }
    modify fun ccs => { ccs with entries := ccs.entries.insert e₁ newN₁ }
    let parentsToPropagate ← removeParents e₁Root
    let lambdas₁ ← getEqcLambdas e₁Root
    let lambdas₂ ← getEqcLambdas e₂Root
    let fnRoots₂ ← if !lambdas₁.isEmpty then collectFnRoots e₂Root else pure #[]
    let fnRoots₁ ← if !lambdas₂.isEmpty then collectFnRoots e₁Root else pure #[]
    let propagate := e₂Root.isConstOf ``True || e₂Root.isConstOf ``False
    let mut toPropagate : Array Expr := #[]
    let mut it := e₁
    repeat
      let some itN ← getEntry it | failure
      if propagate then
        toPropagate := toPropagate.push it
      let newItN : Entry := { itN with root := e₂Root }
      modify fun ccs => { ccs with entries := ccs.entries.insert it newItN }
      it := newItN.next
    until it == e₁
    reinsertParents e₁Root
    let some r₁ ← getEntry e₁Root | failure
    let some r₂ ← getEntry e₂Root | failure
    guard (r₁.root == e₂Root)
    let acVar?₁ := r₁.acVar
    let acVar?₂ := r₂.acVar
    let newR₁ : Entry :=
      { r₁ with
        next := r₂.next }
    let newR₂ : Entry :=
      { r₂ with
        next := r₁.next
        size := r₂.size + r₁.size
        hasLambdas := r₂.hasLambdas || r₁.hasLambdas
        heqProofs := r₂.heqProofs || heqProof
        acVar := acVar?₂ <|> acVar?₁ }
    modify fun ccs =>
      { ccs with
        entries :=
          ccs.entries.insert e₁Root newR₁ |>.insert e₂Root newR₂ }
    checkInvariant
    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₂ lambdas₁
    let lambdaAppsToInternalize ← propagateBetaToEqc fnRoots₁ lambdas₂ lambdaAppsToInternalize
    let constructorEq := r₁.constructor && r₂.constructor
    if let some ps₁ := (← get).parents.find? e₁Root then
      let mut ps₂ : ParentOccSet := ∅
      if let some it' := (← get).parents.find? e₂Root then
        ps₂ := it'
      for p in ps₁ do
        if ← pure p.expr.isApp <||> isCgRoot p.expr then
          if !constructorEq && r₂.constructor then
            propagateProjectionConstructor p.expr e₂Root
          ps₂ := ps₂.insert p
      modify fun ccs =>
        { ccs with
          parents := ccs.parents.erase e₁Root |>.insert e₂Root ps₂ }
    if !(← get).inconsistent then
      if let some acVar₁ := acVar?₁ then
      if let some acVar₂ := acVar?₂ then
        addACEq acVar₁ acVar₂
    if !(← get).inconsistent && constructorEq then
      propagateConstructorEq e₁Root e₂Root
    if !(← get).inconsistent && valueInconsistency then
      propagateValueInconsistency e₁Root e₂Root
    if !(← get).inconsistent then
      updateMT e₂Root
      checkNewSubsingletonEq e₁Root e₂Root
    if !(← get).inconsistent then
      for p in parentsToPropagate do
        propagateUp p
    if !(← get).inconsistent && !toPropagate.isEmpty then
      for e in toPropagate do
        propagateDown e
      if let some phandler := (← get).phandler then
        phandler.propagated toPropagate
    if !(← get).inconsistent then
      for e in lambdaAppsToInternalize do
        internalizeCore e none
    let ccs ← get
    trace[Meta.Tactic.cc.merge] "{e₁Root} = {e₂Root}"
    trace[Debug.Meta.Tactic.cc] "merged: {e₁Root} = {e₂Root}\n{ccs.ppEqcs}"
    trace[Debug.Meta.Tactic.cc.parentOccs] ccs.ppParentOccs
def processTodo : CCM Unit := do
  repeat
    let todo ← getTodo
    let some (lhs, rhs, H, heqProof) := todo.back? | return
    if (← get).inconsistent then
      modifyTodo fun _ => #[]
      return
    modifyTodo Array.pop
    addEqvStep lhs rhs H heqProof
def internalize (e : Expr) : CCM Unit := do
  internalizeCore e none
  processTodo
def addEqvCore (lhs rhs H : Expr) (heqProof : Bool) : CCM Unit := do
  pushTodo lhs rhs H heqProof
  processTodo
def add (type : Expr) (proof : Expr) : CCM Unit := do
  if (← get).inconsistent then return
  modifyTodo fun _ => #[]
  let (isNeg, p) :=
    match type with
    | .app (.const ``Not []) a => (true, a)
    | .forallE _ a (.const ``False []) _ => (true, a)
    | .app (.app (.app (.const ``Ne [u]) α) lhs) rhs =>
      (true, .app (.app (.app (.const ``Eq [u]) α) lhs) rhs)
    | e => (false, e)
  match p with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
    if isNeg then
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs proof false
  | .app (.app (.app (.app (.const ``HEq _) _) lhs) _) rhs =>
    if isNeg then
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse proof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs proof true
  | .app (.app (.const ``Iff _) lhs) rhs =>
    if isNeg then
      let neqProof ← mkAppM ``neq_of_not_iff #[proof]
      internalizeCore p none
      addEqvCore p (.const ``False []) (← mkEqFalse neqProof) false
    else
      internalizeCore lhs none
      internalizeCore rhs none
      addEqvCore lhs rhs (mkApp3 (.const ``propext []) lhs rhs proof) false
  | _ =>
    if ← pure isNeg <||> isProp p then
      internalizeCore p none
      if isNeg then
        addEqvCore p (.const ``False []) (← mkEqFalse proof) false
      else
        addEqvCore p (.const ``True []) (← mkEqTrue proof) false
end CCM
end Mathlib.Tactic.CC
set_option linter.style.longFile 2300