import Lean.Elab.Tactic.Config
import Lean.Elab.Tactic.Location
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.Expr
namespace Mathlib.Tactic
open Lean Meta Elab Parser.Tactic Elab.Tactic
initialize registerTraceClass `Tactic.generalize_proofs
namespace GeneralizeProofs
structure Config where
  maxDepth : Nat := 8
  abstract : Bool := true
  debug : Bool := false
declare_config_elab elabConfig Config
structure GState where
  propToFVar : ExprMap Expr
abbrev MGen := ReaderT Config <| StateRefT GState MetaM
def MGen.insertFVar (prop fvar : Expr) : MGen Unit :=
  modify fun s ↦ { s with propToFVar := s.propToFVar.insert prop fvar }
structure AContext where
  fvars : Array Expr := #[]
  propToFVar : ExprMap Expr
  depth : Nat := 0
  initLCtx : LocalContext
  config : Config
structure AState where
  generalizations : Array (Expr × Expr) := #[]
  propToProof : ExprMap Expr := {}
abbrev MAbs := ReaderT AContext <| MonadCacheT (Expr × Option Expr) Expr <| StateRefT AState MetaM
def MGen.runMAbs {α : Type} (mx : MAbs α) : MGen (α × Array (Expr × Expr)) := do
  let s ← get
  let (x, s') ← mx
    |>.run { initLCtx := ← getLCtx, propToFVar := s.propToFVar, config := (← read) }
    |>.run |>.run {}
  return (x, s'.generalizations)
def MAbs.findProof? (prop : Expr) : MAbs (Option Expr) := do
  if let some pf := (← read).propToFVar[prop]? then
    return pf
  else
    return (← get).propToProof[prop]?
def MAbs.insertProof (prop pf : Expr) : MAbs Unit := do
  if (← read).config.debug then
    unless ← isDefEq prop (← inferType pf) do
      throwError "insertProof: proof{indentD pf}does not have type{indentD prop}"
    unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
      throwError "insertProof: proof{indentD pf}\nis not well-formed in the initial context\n\
        fvars: {(← read).fvars}"
    unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx prop do
      throwError "insertProof: proof{indentD prop}\nis not well-formed in the initial context\n\
        fvars: {(← read).fvars}"
  modify fun s ↦
    { s with
      generalizations := s.generalizations.push (prop, pf)
      propToProof := s.propToProof.insert prop pf }
def MAbs.withLocal {α : Type} (fvar : Expr) (x : MAbs α) : MAbs α :=
  withReader (fun r => {r with fvars := r.fvars.push fvar}) x
def MAbs.withRecurse {α : Type} (x : MAbs α) : MAbs α := do
  withLCtx (← read).initLCtx (← getLocalInstances) do
    withReader (fun r => {r with fvars := #[], depth := r.depth + 1}) x
def appArgExpectedTypes (f : Expr) (args : Array Expr) (ty? : Option Expr) :
    MetaM (Array (Option Expr)) :=
  withTransparency .all <| withNewMCtxDepth do
    (guard ty?.isSome *> go f args ty?) <|> go f args none
where
  go (f : Expr) (args : Array Expr) (ty? : Option Expr) : MetaM (Array (Option Expr)) := do
    let mut margs := #[]
    let mut fty ← inferType f
    let mut unifiedFTy := false
    for i in [0 : args.size] do
      unless i < margs.size do
        let (margs', _, fty') ← forallMetaBoundedTelescope fty (args.size - i)
        if margs'.isEmpty then throwError "could not make progress at argument {i}"
        fty := fty'
        margs := margs ++ margs'
      let arg := args[i]!
      let marg := margs[i]!
      if !unifiedFTy && margs.size == args.size then
        if let some ty := ty? then
          unifiedFTy := (← observing? <| isDefEq fty ty).getD false 
      unless ← isDefEq (← inferType marg) (← inferType arg) do
        throwError s!"failed isDefEq types {i}, {← ppExpr marg}, {← ppExpr arg}"
      unless ← isDefEq marg arg do
        throwError s!"failed isDefEq values {i}, {← ppExpr marg}, {← ppExpr arg}"
      unless ← marg.mvarId!.isAssigned do
        marg.mvarId!.assign arg
    margs.mapM fun marg => do
      return (← instantiateMVars (← inferType marg)).cleanupAnnotations
def mkLambdaFVarsUsedOnly (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let i := fvars.size - i' - 1
    let fvar := fvars[i]!
    e ← mkLambdaFVars #[fvar] e
    match e with
    | .letE _ _ v b _ =>
      e := b.instantiate1 v
    | .lam _ _ b _ =>
      if b.hasLooseBVars then
        fvars' := fvar :: fvars'
      else
        e := b
    | _ => unreachable!
  return (fvars'.toArray, e)
partial def abstractProofs (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then
    MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else
    return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    trace[Tactic.generalize_proofs] "visit (fvars := {(← read).fvars}) e is {e}"
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← whnfD ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then
      return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    trace[Tactic.generalize_proofs] "before mkLambdaFVarsUsedOnly, e = {e}\nfvars={fvars}"
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      trace[Tactic.generalize_proofs] "'abstract' is false and proof uses fvars, not abstracting"
      return eOrig
    trace[Tactic.generalize_proofs] "after mkLambdaFVarsUsedOnly, pf = {pf}\nfvars'={fvars'}"
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs pfTy none
    trace[Tactic.generalize_proofs] "finding {pfTy}"
    if let some pf' ← MAbs.findProof? pfTy then
      trace[Tactic.generalize_proofs] "found proof"
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    trace[Tactic.generalize_proofs] "added proof"
    return mkAppN pf fvars'
def initialPropToFVar : MetaM (ExprMap Expr) := do
  (← getLCtx).foldrM (init := {}) fun decl m => do
    if !decl.isImplementationDetail then
      let ty := (← instantiateMVars decl.type).cleanupAnnotations
      if ← Meta.isProp ty then
        return m.insert ty decl.toExpr
    return m
partial def withGeneralizedProofs {α : Type} [Nonempty α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  trace[Tactic.generalize_proofs] "pre-abstracted{indentD e}\npropToFVar: {propToFVar.toArray}"
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs e ty?
  trace[Tactic.generalize_proofs] "\
    post-abstracted{indentD e}\nnew generalizations: {generalizations}"
  let rec
    go [Nonempty α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          trace[Tactic.generalize_proofs] "after: e' = {e}"
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)
partial def generalizeProofsCore
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) :=
  go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      trace[Tactic.generalize_proofs] "generalizeProofsCore {i}{g}\n{(← get).propToFVar.toArray}"
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := tgt.bindingDomain!.cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.bindingName! ty tgt.bindingBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar[ty]? then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs t none fun hs' pfs' t' => do
            withGeneralizedProofs v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g') (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      trace[Tactic.generalize_proofs] "\
        generalizeProofsCore target{g}\n{(← get).propToFVar.toArray}"
      withGeneralizedProofs (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)
end GeneralizeProofs
partial def _root_.Lean.MVarId.generalizeProofs
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : GeneralizeProofs.Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← GeneralizeProofs.initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore g fvars rfvars target |>.run config |>.run' s
elab (name := generalizeProofsElab) "generalize_proofs" config:Parser.Tactic.optConfig
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← GeneralizeProofs.elabConfig config
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← g.generalizeProofs fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      withLCtx lctx (← getLocalInstances) do
        let g' ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!
end Mathlib.Tactic