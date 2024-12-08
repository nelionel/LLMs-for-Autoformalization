import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Refl
import Mathlib.Logic.IsEmpty
namespace Lean.Meta
initialize registerTraceClass `Meta.CongrTheorems
def mkHCongrWithArity' (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let thm ← mkHCongrWithArity f numArgs
  process thm thm.type thm.argKinds.toList #[] #[] #[] #[]
where
  process (cthm : CongrTheorem) (type : Expr) (argKinds : List CongrArgKind)
      (argKinds' : Array CongrArgKind) (params args : Array Expr)
      (letArgs : Array (Expr × Expr)) : MetaM CongrTheorem := do
    match argKinds with
    | [] =>
      if letArgs.isEmpty then
        return cthm
      else
        let proof := letArgs.foldr (init := mkAppN cthm.proof args) (fun (fvar, val) proof =>
          (proof.abstract #[fvar]).instantiate1 val)
        let pf' ← mkLambdaFVars params proof
        return {proof := pf', type := ← inferType pf', argKinds := argKinds'}
    | argKind :: argKinds =>
      match argKind with
      | .eq | .heq =>
        forallBoundedTelescope type (some 3) fun params' type' => do
          let #[x, y, eq] := params' | unreachable!
          let g := (← mkFreshExprMVar (← inferType eq)).mvarId!
          let g ← g.clear eq.fvarId!
          if (← observing? <| prove g args).isSome then
            let eqPf ← instantiateMVars (.mvar g)
            process cthm type' argKinds (argKinds'.push .subsingletonInst)
              (params := params ++ #[x, y]) (args := args ++ params')
              (letArgs := letArgs.push (eq, eqPf))
          else
            process cthm type' argKinds (argKinds'.push argKind)
              (params := params ++ params') (args := args ++ params')
              (letArgs := letArgs)
      | _ => panic! "Unexpected CongrArgKind"
  prove (g : MVarId) (params : Array Expr) : MetaM Unit := do
    let g ← g.cleanup
    let [g] ← g.casesRec fun localDecl => do
      return (localDecl.type.isEq || localDecl.type.isHEq) && params.contains localDecl.toExpr
      | failure
    try g.refl; return catch _ => pure ()
    try g.hrefl; return catch _ => pure ()
    if ← g.proofIrrelHeq then return
    let g ← g.heqOfEq
    if ← g.subsingletonElim then return
    failure
universe u v
class FastSubsingleton (α : Sort u) : Prop where
  [inst : Subsingleton α]
class FastIsEmpty (α : Sort u) : Prop where
  [inst : IsEmpty α]
protected theorem FastSubsingleton.elim {α : Sort u} [h : FastSubsingleton α] : (a b : α) → a = b :=
  h.inst.allEq
instance (priority := 100) {α : Type u} [inst : FastIsEmpty α] : FastSubsingleton α where
  inst := have := inst.inst; inferInstance
instance {p : Prop} : FastSubsingleton p := {}
instance {p : Prop} : FastSubsingleton (Decidable p) := {}
instance : FastSubsingleton (Fin 1) := {}
instance : FastSubsingleton PUnit := {}
instance : FastIsEmpty Empty := {}
instance : FastIsEmpty False := {}
instance : FastIsEmpty (Fin 0) := {}
instance {α : Sort u} [inst : FastIsEmpty α] {β : (x : α) → Sort v} :
    FastSubsingleton ((x : α) → β x) where
  inst.allEq _ _ := funext fun a => (inst.inst.false a).elim
instance {α : Sort u} {β : (x : α) → Sort v} [inst : ∀ x, FastSubsingleton (β x)] :
    FastSubsingleton ((x : α) → β x) where
  inst := have := fun x ↦ (inst x).inst; inferInstance
def withSubsingletonAsFast {α : Type} [Inhabited α] (mx : (Expr → Expr) → MetaM α) : MetaM α := do
  let insts1 := (← getLocalInstances).filter fun inst => inst.className == ``Subsingleton
  let insts2 := (← getLocalInstances).filter fun inst => inst.className == ``IsEmpty
  let mkInst (f : Name) (inst : Expr) : MetaM Expr := do
    forallTelescopeReducing (← inferType inst) fun args _ => do
      mkLambdaFVars args <| ← mkAppOptM f #[none, mkAppN inst args]
  let vals := (← insts1.mapM fun inst => mkInst ``FastSubsingleton.mk inst.fvar)
    ++ (← insts2.mapM fun inst => mkInst ``FastIsEmpty.mk inst.fvar)
  let tys ← vals.mapM inferType
  withLocalDeclsD (tys.map fun ty => (`inst, fun _ => pure ty)) fun args =>
    withNewLocalInstances args 0 do
      let elim (e : Expr) : Expr := e.replaceFVars args vals
      mx elim
def fastSubsingletonElim (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `fastSubsingletonElim
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, rhs) := tgt.eq? | failure
      let pf ← withSubsingletonAsFast fun elim =>
        elim <$> mkAppM ``FastSubsingleton.elim #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false
partial def mkRichHCongr (fType : Expr) (info : FunInfo)
    (fixedFun : Bool := false) (fixedParams : Array Bool := #[])
    (forceHEq : Bool := false) :
    MetaM CongrTheorem := do
  trace[Meta.CongrTheorems] "ftype: {fType}"
  trace[Meta.CongrTheorems] "deps: {info.paramInfo.map (fun p => p.backDeps)}"
  trace[Meta.CongrTheorems] "fixedFun={fixedFun}, fixedParams={fixedParams}"
  doubleTelescope fType info.getArity fixedParams fun xs ys fixedParams => do
    trace[Meta.CongrTheorems] "xs = {xs}"
    trace[Meta.CongrTheorems] "ys = {ys}"
    trace[Meta.CongrTheorems] "computed fixedParams={fixedParams}"
    let lctx := (← getLCtx) 
    withLocalDeclD `f fType fun ef => withLocalDeclD `f' fType fun pef' => do
    let ef' := if fixedFun then ef else pef'
    withLocalDeclD `e (← mkEq ef ef') fun ee => do
    withNewEqs xs ys fixedParams fun kinds eqs => do
      let fParams := if fixedFun then #[ef] else #[ef, ef', ee]
      let mut hs := fParams     
      let mut hs' := fParams    
      let mut vals' := fParams  
      for i in [0 : info.getArity] do
        hs := hs.push xs[i]!
        hs' := hs'.push xs[i]!
        vals' := vals'.push xs[i]!
        if let some (eq, eq', val) := eqs[i]! then
          hs := hs.push ys[i]! |>.push eq
          hs' := hs'.push ys[i]! |>.push eq'
          vals' := vals'.push ys[i]! |>.push val
      let mkConcl := if forceHEq then mkHEq else mkEqHEq
      let congrType ← mkForallFVars hs (← mkConcl (mkAppN ef xs) (mkAppN ef' ys))
      trace[Meta.CongrTheorems] "simple congrType: {congrType}"
      let some proof ← withLCtx lctx (← getLocalInstances) <| trySolve congrType
        | throwError "Internal error when constructing congruence lemma proof"
      let mut hs'' := #[] 
      let mut pfVars := #[] 
      let mut pfVals := #[] 
      let mut kinds' : Array CongrArgKind := #[if fixedFun then .fixed else .eq]
      for i in [0 : info.getArity] do
        hs'' := hs''.push xs[i]!
        if let some (_, eq', _) := eqs[i]! then
          hs'' := hs''.push ys[i]!
          let pf? ← withLCtx lctx (← getLocalInstances) <| trySolve (← inferType eq')
          if let some pf := pf? then
            pfVars := pfVars.push eq'
            pfVals := pfVals.push pf
            kinds' := kinds'.push .subsingletonInst
          else
            hs'' := hs''.push eq'
            kinds' := kinds'.push kinds[i]!
        else
          kinds' := kinds'.push .fixed
      trace[Meta.CongrTheorems] "CongrArgKinds: {repr kinds'}"
      let proof' ← mkLambdaFVars fParams (← mkLambdaFVars (usedOnly := true) hs''
                    (mkAppN (← mkLambdaFVars pfVars (proof.beta vals')) pfVals))
      let congrType' ← inferType proof'
      trace[Meta.CongrTheorems] "rich congrType: {congrType'}"
      return {proof := proof', type := congrType', argKinds := kinds'}
where
  doubleTelescope {α} (fty : Expr) (numVars : Nat) (fixed : Array Bool)
      (k : Array Expr → Array Expr → Array Bool → MetaM α) : MetaM α := do
    let rec loop (i : Nat)
        (ftyx ftyy : Expr) (xs ys : Array Expr) (fixed' : Array Bool) : MetaM α := do
      if i < numVars then
        let ftyx ← whnfD ftyx
        let ftyy ← whnfD ftyy
        unless ftyx.isForall do
          throwError "doubleTelescope: function doesn't have enough parameters"
        withLocalDeclD ftyx.bindingName! ftyx.bindingDomain! fun fvarx => do
          let ftyx' := ftyx.bindingBody!.instantiate1 fvarx
          if fixed.getD i false && ftyx.bindingDomain! == ftyy.bindingDomain! then
            let ftyy' := ftyy.bindingBody!.instantiate1 fvarx
            loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvarx) (fixed'.push true)
          else
            let yname := ftyy.bindingName!.appendAfter "'"
            withLocalDeclD yname ftyy.bindingDomain! fun fvary => do
              let ftyy' := ftyy.bindingBody!.instantiate1 fvary
              loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvary) (fixed'.push false)
      else
        k xs ys fixed'
    loop 0 fty fty #[] #[] #[]
  withNewEqs {α} (xs ys : Array Expr) (fixedParams : Array Bool)
      (k : Array CongrArgKind → Array (Option (Expr × Expr × Expr)) → MetaM α) : MetaM α :=
    let rec loop (i : Nat)
        (kinds : Array CongrArgKind) (eqs : Array (Option (Expr × Expr × Expr))) := do
      if i < xs.size then
        let x := xs[i]!
        let y := ys[i]!
        if fixedParams[i]! then
          loop (i+1) (kinds.push .fixed) (eqs.push none)
        else
          let deps := info.paramInfo[i]!.backDeps.filterMap (fun j => eqs[j]!)
          let eq' ← mkForallFVars (deps.map fun (eq, _, _) => eq) (← mkEqHEq x y)
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkEqHEq x y) fun h =>
          withLocalDeclD ((`e').appendIndexAfter (i+1)) eq' fun h' => do
            let v := mkAppN h' (deps.map fun (_, _, val) => val)
            let kind := if (← inferType h).eq?.isSome then .eq else .heq
            loop (i+1) (kinds.push kind) (eqs.push (h, h', v))
      else
        k kinds eqs
    loop 0 #[] #[]
  trySolveCore (mvarId : MVarId) : MetaM Unit := do
    let mvarId ← mvarId.cleanup
    let (_, mvarId) ← mvarId.intros
    let mvarId := (← mvarId.substEqs).getD mvarId
    try mvarId.refl; return catch _ => pure ()
    try mvarId.hrefl; return catch _ => pure ()
    if ← mvarId.proofIrrelHeq then return
    let mvarId ← mvarId.heqOfEq
    if ← fastSubsingletonElim mvarId then return
    throwError "was not able to solve for proof"
  trySolve (ty : Expr) : MetaM (Option Expr) := observing? do
    let mvar ← mkFreshExprMVar ty
    trace[Meta.CongrTheorems] "trySolve {mvar.mvarId!}"
    withReducible <| trySolveCore mvar.mvarId!
    trace[Meta.CongrTheorems] "trySolve success!"
    let pf ← instantiateMVars mvar
    return pf
end Lean.Meta