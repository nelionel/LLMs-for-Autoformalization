import Mathlib.Lean.Expr.Rat
import Mathlib.Tactic.NormNum.Result
import Mathlib.Util.Qq
import Lean.Elab.Tactic.Location
open Lean
open Lean.Meta Qq Lean.Elab Term
syntax (name := norm_num) "norm_num " term,+ : attr
namespace Mathlib
namespace Meta.NormNum
initialize registerTraceClass `Tactic.norm_num
structure NormNumExt where
  pre := true
  post := true
  eval {u : Level} {α : Q(Type u)} (e : Q($α)) : MetaM (Result e)
  name : Name := by exact decl_name%
variable {u : Level}
def mkNormNumExt (n : Name) : ImportM NormNumExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n
abbrev Entry := Array (Array DiscrTree.Key) × Name
structure NormNums where
  tree : DiscrTree NormNumExt := {}
  erased : PHashSet Name := {}
  deriving Inhabited
initialize normNumExt : ScopedEnvExtension Entry (Entry × NormNumExt) NormNums ←
  have : BEq NormNumExt := ⟨fun _ _ ↦ false⟩
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertCore ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkNormNumExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) ↦
      { tree := insert kss ext tree, erased := erased.erase n }
  }
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isRawNatLit then
    let lit : Q(ℕ) := e
    return .isNat (q(instAddMonoidWithOneNat) : Q(AddMonoidWithOne ℕ))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    let arr ← normNums.tree.getMatch e
    for ext in arr do
      if (bif post then ext.post else ext.pre) && ! normNums.erased.contains ext.name then
        try
          let new ← withReducibleAndInstances <| ext.eval e
          trace[Tactic.norm_num] "{ext.name}:\n{e} ==> {new}"
          return new
        catch err =>
          trace[Tactic.norm_num] "{ext.name} failed {e}: {err.toMessageData}"
          s.restore
    throwError "{e}: no norm_nums apply"
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩
def deriveInt {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Ring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℤ)) × Q(IsInt $e $lit)) := do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩
def deriveRat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(DivisionRing $α) := by with_reducible assumption) :
    MetaM (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(IsRat $e $n $d)) := do
  let some res := (← derive e).toRat' | failure
  pure res
def deriveBool (p : Q(Prop)) : MetaM ((b : Bool) × BoolResult p b) := do
  let .isBool b prf ← derive (α := (q(Prop) : Q(Type))) p | failure
  pure ⟨b, prf⟩
def deriveBoolOfIff (p p' : Q(Prop)) (hp : Q($p ↔ $p')) :
    MetaM ((b : Bool) × BoolResult p' b) := do
  let ⟨b, pb⟩ ← deriveBool p
  match b with
  | true  => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩
def eval (e : Expr) (post := false) : MetaM Simp.Result := do
  if e.isExplicitNumber then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult
def NormNums.eraseCore (d : NormNums) (declName : Name) : NormNums :=
 { d with erased := d.erased.insert declName }
def NormNums.erase {m : Type → Type} [Monad m] [MonadError m] (d : NormNums) (declName : Name) :
    m NormNums := do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName
initialize registerBuiltinAttribute {
  name := `norm_num
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| norm_num $es,*) => do
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return 
      let ext ← mkNormNumExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      normNumExt.add ((keys, declName), ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := normNumExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => normNumExt.modifyState env fun _ => s
}
def tryNormNum (post := false) (e : Expr) : SimpM Simp.Step := do
  try
    return .done (← eval e post)
  catch _ =>
    return .continue
variable (ctx : Simp.Context) (useSimp := true) in
mutual
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := Simp.preDefault #[] >> tryNormNum
      post := Simp.postDefault #[] >> tryNormNum (post := true)
      discharge? := discharge
    } else {
      pre := tryNormNum
      post := tryNormNum (post := true)
      discharge? := discharge
    }
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
end
def normNumAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := ctx.setSimpTheorems (ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId))
    let r ← deriveSimp ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← deriveSimp ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId ↦ !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)
open Tactic in
def getSimpContext (cfg args : Syntax) (simpOnly := false) : TacticM Simp.Context := do
  let config ← elabSimpConfigCore cfg
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, simprocs := _, starArg } ←
    elabSimpArgs args[0] (eraseLocal := false) (kind := .simp) (simprocs := {})
      (← Simp.mkContext config (simpTheorems := #[simpTheorems])
        (congrTheorems := ← getSimpCongrTheorems))
  unless starArg do return ctx
  let mut simpTheorems := ctx.simpTheorems
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
  return ctx.setSimpTheorems simpTheorems
open Elab.Tactic in
def elabNormNum (cfg args loc : Syntax) (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let ctx ← getSimpContext cfg args (!useSimp || simpOnly)
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => normNumAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => normNumAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]
end Meta.NormNum
namespace Tactic
open Lean.Parser.Tactic Meta.NormNum
elab (name := normNum)
    "norm_num" cfg:optConfig only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum cfg args loc (simpOnly := only.isSome) (useSimp := true)
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode mkNullNode loc (simpOnly := true) (useSimp := false)
open Lean Elab Tactic
@[inherit_doc normNum1] syntax (name := normNum1Conv) "norm_num1" : conv
@[tactic normNum1Conv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))
@[inherit_doc normNum] syntax (name := normNumConv)
    "norm_num" optConfig &" only"? (simpArgs)? : conv
@[tactic normNumConv] def elabNormNumConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[1] stx[3] !stx[2].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))
macro (name := normNumCmd) "#norm_num" cfg:optConfig o:(&" only")?
    args:(Parser.Tactic.simpArgs)? " :"? ppSpace e:term : command =>
  `(command| #conv norm_num $cfg:optConfig $[only%$o]? $(args)? => $e)
end Mathlib.Tactic