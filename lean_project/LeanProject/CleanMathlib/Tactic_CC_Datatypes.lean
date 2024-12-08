import Lean.Meta.CongrTheorems
import Lean.Meta.Tactic.Rfl
import Batteries.Data.RBMap.Basic
import Mathlib.Lean.Meta.Basic
import Std.Data.HashMap.Basic
universe u
open Lean Meta Elab Tactic
namespace Mathlib.Tactic.CC
def isValue (e : Expr) : Bool :=
  e.int?.isSome || e.isCharLit || e.isStringLit
def isInterpretedValue (e : Expr) : MetaM Bool := do
  if e.isCharLit || e.isStringLit then
    return true
  else if e.int?.isSome then
    let type ← inferType e
    pureIsDefEq type (.const ``Nat []) <||> pureIsDefEq type (.const ``Int [])
  else
    return false
def liftFromEq (R : Name) (H : Expr) : MetaM Expr := do
  if R == ``Eq then return H
  let HType ← whnf (← inferType H)
  let some (A, a, _) := HType.eq?
    | throwError "failed to build liftFromEq equality proof expected: {H}"
  let motive ←
    withLocalDeclD `x A fun x => do
      let hType ← mkEq a x
      withLocalDeclD `h hType fun h =>
        mkRel R a x >>= mkLambdaFVars #[x, h]
  let minor ← do
    let mt ← mkRel R a a
    let m ← mkFreshExprSyntheticOpaqueMVar mt
    m.mvarId!.applyRfl
    instantiateMVars m
  mkEqRec motive minor H
scoped instance : Ord Expr where
  compare a b := bif Expr.lt a b then .lt else bif Expr.eqv b a then .eq else .gt
abbrev RBExprMap (α : Type u) := Batteries.RBMap Expr α compare
abbrev RBExprSet := Batteries.RBSet Expr compare
structure CCCongrTheorem extends CongrTheorem where
  heqResult : Bool := false
  hcongrTheorem : Bool := false
def mkCCHCongrWithArity (fn : Expr) (nargs : Nat) : MetaM (Option CCCongrTheorem) := do
  let eqCongr ← try mkHCongrWithArity fn nargs catch _ => return none
  return some { eqCongr with
    heqResult := true
    hcongrTheorem := true }
structure CCCongrTheoremKey where
  fn : Expr
  nargs : Nat
  deriving BEq, Hashable
abbrev CCCongrTheoremCache := Std.HashMap CCCongrTheoremKey (Option CCCongrTheorem)
structure CCConfig where
  ignoreInstances : Bool := true
  ac : Bool := true
  hoFns : Option (List Name) := none
  em : Bool := true
  values : Bool := false
  deriving Inhabited
inductive ACApps where
  | ofExpr (e : Expr) : ACApps
  | apps (op : Expr) (args : Array Expr) : ACApps
  deriving Inhabited, BEq
instance : Coe Expr ACApps := ⟨ACApps.ofExpr⟩
attribute [coe] ACApps.ofExpr
scoped instance : Ord ACApps where
  compare
    | .ofExpr a, .ofExpr b => compare a b
    | .ofExpr _, .apps _ _ => .lt
    | .apps _ _, .ofExpr _ => .gt
    | .apps op₁ args₁, .apps op₂ args₂ =>
      compare op₁ op₂ |>.then <| compare args₁.size args₂.size |>.then <| Id.run do
        for i in [:args₁.size] do
          let o := compare args₁[i]! args₂[i]!
          if o != .eq then return o
        return .eq
def ACApps.isSubset : (e₁ e₂ : ACApps) → Bool
  | .ofExpr a, .ofExpr b => a == b
  | .ofExpr a, .apps _ args => args.contains a
  | .apps _ _, .ofExpr _ => false
  | .apps op₁ args₁, .apps op₂ args₂ =>
    if op₁ == op₂ then
      if args₁.size ≤ args₂.size then Id.run do
        let mut i₁ := 0
        let mut i₂ := 0
        while i₁ < args₁.size ∧ i₂ < args₂.size do
          if args₁[i₁]! == args₂[i₂]! then
            i₁ := i₁ + 1
            i₂ := i₂ + 1
          else if Expr.lt args₂[i₂]! args₁[i₁]! then
            i₂ := i₂ + 1
          else return false
        return i₁ == args₁.size
      else false
    else false
def ACApps.diff (e₁ e₂ : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e₁ with
  | .apps op₁ args₁ => Id.run do
    let mut r := r
    match e₂ with
    | .apps op₂ args₂ =>
      if op₁ == op₂ then
        let mut i₂ := 0
        for i₁ in [:args₁.size] do
          if i₂ == args₂.size then
            r := r.push args₁[i₁]!
          else if args₁[i₁]! == args₂[i₂]! then
            i₂ := i₂ + 1
          else
            r := r.push args₁[i₁]!
    | .ofExpr e₂ =>
      let mut found := false
      for i in [:args₁.size] do
        if !found && args₁[i]! == e₂ then
          found := true
        else
          r := r.push args₁[i]!
    return r
  | .ofExpr e => if e₂ == e then r else r.push e
def ACApps.append (op : Expr) (e : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e with
  | .apps op' args =>
    if op' == op then r ++ args else r
  | .ofExpr e =>
    r.push e
def ACApps.intersection (e₁ e₂ : ACApps) (r : Array Expr := #[]) : Array Expr :=
  match e₁, e₂ with
  | .apps _ args₁, .apps _ args₂ => Id.run do
    let mut r := r
    let mut i₁ := 0
    let mut i₂ := 0
    while i₁ < args₁.size ∧ i₂ < args₂.size do
      if args₁[i₁]! == args₂[i₂]! then
        r := r.push args₁[i₁]!
        i₁ := i₁ + 1
        i₂ := i₂ + 1
      else if Expr.lt args₂[i₂]! args₁[i₁]! then
        i₂ := i₂ + 1
      else
        i₁ := i₁ + 1
    return r
  | _, _ => r
def ACApps.mkApps (op : Expr) (args : Array Expr) : ACApps :=
  .apps op (args.qsort Expr.lt)
def ACApps.mkFlatApps (op : Expr) (e₁ e₂ : ACApps) : ACApps :=
  let newArgs := ACApps.append op e₁
  let newArgs := ACApps.append op e₂ newArgs
  ACApps.mkApps op newArgs
def ACApps.toExpr : ACApps → Option Expr
  | .apps _ ⟨[]⟩ => none
  | .apps op ⟨arg₀ :: args⟩ => some <| args.foldl (fun e arg => mkApp2 op e arg) arg₀
  | .ofExpr e => some e
abbrev RBACAppsMap (α : Type u) := Batteries.RBMap ACApps α compare
abbrev RBACAppsSet := Batteries.RBSet ACApps compare
inductive DelayedExpr where
  | ofExpr (e : Expr) : DelayedExpr
  | eqProof (lhs rhs : Expr) : DelayedExpr
  | congrArg (f : Expr) (h : DelayedExpr) : DelayedExpr
  | congrFun (h : DelayedExpr) (a : ACApps) : DelayedExpr
  | eqSymm (h : DelayedExpr) : DelayedExpr
  | eqSymmOpt (a₁ a₂ : ACApps) (h : DelayedExpr) : DelayedExpr
  | eqTrans (h₁ h₂ : DelayedExpr) : DelayedExpr
  | eqTransOpt (a₁ a₂ a₃ : ACApps) (h₁ h₂ : DelayedExpr) : DelayedExpr
  | heqOfEq (h : DelayedExpr) : DelayedExpr
  | heqSymm (h : DelayedExpr) : DelayedExpr
  deriving Inhabited
instance : Coe Expr DelayedExpr := ⟨DelayedExpr.ofExpr⟩
attribute [coe] DelayedExpr.ofExpr
inductive EntryExpr
  | ofExpr (e : Expr) : EntryExpr
  | congr : EntryExpr
  | eqTrue : EntryExpr
  | refl : EntryExpr
  | ofDExpr (e : DelayedExpr) : EntryExpr
  deriving Inhabited
instance : ToMessageData EntryExpr where
  toMessageData
  | .ofExpr e => toMessageData e
  | .congr => m!"[congruence proof]"
  | .eqTrue => m!"[eq_true proof]"
  | .refl => m!"[refl proof]"
  | .ofDExpr _ => m!"[delayed expression]"
instance : Coe Expr EntryExpr := ⟨EntryExpr.ofExpr⟩
attribute [coe] EntryExpr.ofExpr
structure Entry where
  next : Expr
  root : Expr
  cgRoot : Expr
  target : Option Expr := none
  proof : Option EntryExpr := none
  acVar : Option Expr := none
  flipped : Bool
  interpreted : Bool
  constructor : Bool
  hasLambdas : Bool
  heqProofs : Bool
  fo : Bool
  size : Nat
  mt : Nat
  deriving Inhabited
abbrev Entries := RBExprMap Entry
structure ACEntry where
  idx : Nat
  RLHSOccs : RBACAppsSet := ∅
  RRHSOccs : RBACAppsSet := ∅
  deriving Inhabited
def ACEntry.ROccs (ent : ACEntry) : (inLHS : Bool) → RBACAppsSet
  | true => ent.RLHSOccs
  | false => ent.RRHSOccs
structure ParentOcc where
  expr : Expr
  symmTable : Bool
abbrev ParentOccSet := Batteries.RBSet ParentOcc (Ordering.byKey ParentOcc.expr compare)
abbrev Parents := RBExprMap ParentOccSet
inductive CongruencesKey
  | fo (fn : Expr) (args : Array Expr) : CongruencesKey
  | ho (fn : Expr) (arg : Expr) : CongruencesKey
  deriving BEq, Hashable
abbrev Congruences := Std.HashMap CongruencesKey (List Expr)
structure SymmCongruencesKey where
  (h₁ h₂ : Expr)
  deriving BEq, Hashable
abbrev SymmCongruences := Std.HashMap SymmCongruencesKey (List (Expr × Name))
abbrev SubsingletonReprs := RBExprMap Expr
abbrev InstImplicitReprs := RBExprMap (List Expr)
abbrev TodoEntry := Expr × Expr × EntryExpr × Bool
abbrev ACTodoEntry := ACApps × ACApps × DelayedExpr
structure CCState extends CCConfig where
  entries : Entries := ∅
  parents : Parents := ∅
  congruences : Congruences := ∅
  symmCongruences : SymmCongruences := ∅
  subsingletonReprs : SubsingletonReprs := ∅
  instImplicitReprs : InstImplicitReprs := ∅
  frozePartitions : Bool := false
  canOps : RBExprMap Expr := ∅
  opInfo : RBExprMap Bool := ∅
  acEntries : RBExprMap ACEntry := ∅
  acR : RBACAppsMap (ACApps × DelayedExpr) := ∅
  inconsistent : Bool := false
  gmt : Nat := 0
  deriving Inhabited
attribute [inherit_doc SubsingletonReprs] CCState.subsingletonReprs
def CCState.mkEntryCore (ccs : CCState) (e : Expr) (interpreted : Bool) (constructor : Bool) :
    CCState :=
  assert! ccs.entries.find? e |>.isNone
  let n : Entry :=
    { next := e
      root := e
      cgRoot := e
      size := 1
      flipped := false
      interpreted
      constructor
      hasLambdas := e.isLambda
      heqProofs := false
      mt := ccs.gmt
      fo := false }
  { ccs with entries := ccs.entries.insert e n }
namespace CCState
def root (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries.find? e with
  | some n => n.root
  | none => e
def next (ccs : CCState) (e : Expr) : Expr :=
  match ccs.entries.find? e with
  | some n => n.next
  | none => e
def isCgRoot (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries.find? e with
  | some n => e == n.cgRoot
  | none => true
def mt (ccs : CCState) (e : Expr) : Nat :=
  match ccs.entries.find? e with
  | some n => n.mt
  | none => ccs.gmt
def inSingletonEqc (ccs : CCState) (e : Expr) : Bool :=
  match ccs.entries.find? e with
  | some it => it.next == e
  | none => true
def getRoots (ccs : CCState) (roots : Array Expr) (nonsingletonOnly : Bool) : Array Expr :=
  Id.run do
    let mut roots := roots
    for (k, n) in ccs.entries do
      if k == n.root && (!nonsingletonOnly || !ccs.inSingletonEqc k) then
        roots := roots.push k
    return roots
def checkEqc (ccs : CCState) (e : Expr) : Bool :=
  toBool <| Id.run <| OptionT.run do
    let root := ccs.root e
    let mut size : Nat := 0
    let mut it := e
    repeat
      let some itN := ccs.entries.find? it | failure
      guard (itN.root == root)
      let mut it₂ := it
      repeat
        let it₂N := ccs.entries.find? it₂
        match it₂N.bind Entry.target with
        | some it₃ => it₂ := it₃
        | none => break
      guard (it₂ == root)
      it := itN.next
      size := size + 1
    until it == e
    guard (ccs.entries.find? root |>.any (·.size == size))
def checkInvariant (ccs : CCState) : Bool :=
  ccs.entries.all fun k n => k != n.root || checkEqc ccs k
def getNumROccs (ccs : CCState) (e : Expr) (inLHS : Bool) : Nat :=
  match ccs.acEntries.find? e with
  | some ent => (ent.ROccs inLHS).size
  | none => 0
def getVarWithLeastOccs (ccs : CCState) (e : ACApps) (inLHS : Bool) : Option Expr :=
  match e with
  | .apps _ args => Id.run do
    let mut r := args[0]?
    let mut numOccs := r.casesOn 0 fun r' => ccs.getNumROccs r' inLHS
    for hi : i in [1:args.size] do
      if (args[i]'hi.2) != (args[i - 1]'(Nat.lt_of_le_of_lt (i.sub_le 1) hi.2)) then
        let currOccs := ccs.getNumROccs (args[i]'hi.2) inLHS
        if currOccs < numOccs then
          r := (args[i]'hi.2)
          numOccs := currOccs
    return r
  | .ofExpr e => e
def getVarWithLeastLHSOccs (ccs : CCState) (e : ACApps) : Option Expr :=
  ccs.getVarWithLeastOccs e true
def getVarWithLeastRHSOccs (ccs : CCState) (e : ACApps) : Option Expr :=
  ccs.getVarWithLeastOccs e false
open MessageData
def ppEqc (ccs : CCState) (e : Expr) : MessageData := Id.run do
  let mut lr : List MessageData := []
  let mut it := e
  repeat
    let some itN := ccs.entries.find? it | break
    let mdIt : MessageData :=
      if it.isForall || it.isLambda || it.isLet then paren (ofExpr it) else ofExpr it
    lr := mdIt :: lr
    it := itN.next
  until it == e
  let l := lr.reverse
  return bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"
def ppEqcs (ccs : CCState) (nonSingleton : Bool := true) : MessageData :=
  let roots := ccs.getRoots #[] nonSingleton
  let a := roots.map (fun root => ccs.ppEqc root)
  let l := a.toList
  bracket "{" (group <| joinSep l (ofFormat ("," ++ .line))) "}"
def ppParentOccsAux (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.parents.find? e with
  | some poccs =>
    let r := ofExpr e ++ ofFormat (.line ++ ":=" ++ .line)
    let ps := poccs.toList.map fun o => ofExpr o.expr
    group (r ++ bracket "{" (group <| joinSep ps (ofFormat ("," ++ .line))) "}")
  | none => ofFormat .nil
def ppParentOccs (ccs : CCState) : MessageData :=
  let r := ccs.parents.toList.map fun (k, _) => ccs.ppParentOccsAux k
  bracket "{" (group <| joinSep r (ofFormat ("," ++ .line))) "}"
def ppACDecl (ccs : CCState) (e : Expr) : MessageData :=
  match ccs.acEntries.find? e with
  | some it => group (ofFormat (s!"x_{it.idx}" ++ .line ++ ":=" ++ .line) ++ ofExpr e)
  | none => nil
def ppACDecls (ccs : CCState) : MessageData :=
  let r := ccs.acEntries.toList.map fun (k, _) => ccs.ppACDecl k
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"
def ppACExpr (ccs : CCState) (e : Expr) : MessageData :=
  if let some it := ccs.acEntries.find? e then
    s!"x_{it.idx}"
  else
    ofExpr e
partial def ppACApps (ccs : CCState) : ACApps → MessageData
  | .apps op args =>
    let r := ofExpr op :: args.toList.map fun arg => ccs.ppACExpr arg
    sbracket (joinSep r (ofFormat .line))
  | .ofExpr e => ccs.ppACExpr e
def ppACR (ccs : CCState) : MessageData :=
  let r := ccs.acR.toList.map fun (k, p, _) => group <|
    ccs.ppACApps k ++ ofFormat (Format.line ++ "
  bracket "{" (joinSep r (ofFormat ("," ++ .line))) "}"
def ppAC (ccs : CCState) : MessageData :=
  sbracket (ccs.ppACDecls ++ ofFormat ("," ++ .line) ++ ccs.ppACR)
end CCState
structure CCNormalizer where
  normalize : Expr → MetaM Expr
attribute [inherit_doc CCNormalizer] CCNormalizer.normalize
structure CCPropagationHandler where
  propagated : Array Expr → MetaM Unit
  newAuxCCTerm : Expr → MetaM Unit
structure CCStructure extends CCState where
  todo : Array TodoEntry := #[]
  acTodo : Array ACTodoEntry := #[]
  normalizer : Option CCNormalizer := none
  phandler : Option CCPropagationHandler := none
  cache : CCCongrTheoremCache := ∅
  deriving Inhabited
end Mathlib.Tactic.CC