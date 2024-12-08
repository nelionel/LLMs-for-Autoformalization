import Mathlib.Tactic.Core
import Mathlib.Logic.Equiv.Defs
namespace Mathlib.ProxyType
open Lean Elab Lean.Parser.Term
open Meta Command
initialize registerTraceClass `Elab.ProxyType
structure ProxyEquivConfig where
  proxyName : Name
  proxyEquivName : Name
  mkCtorProxyType : List (Expr × Name) → TermElabM (Expr × Term)
  mkProxyType : Array (Name × Expr × Term) → TermElabM (Expr × Array Term × TSyntax `tactic)
def defaultMkCtorProxyType (xs : List (Expr × Name))
    (decorateSigma : Expr → TermElabM Expr := pure) :
    TermElabM (Expr × Term) :=
  match xs with
  | [] => return (mkConst ``Unit, ← `(term| ()))
  | [(x, a)] => do
    let xty ← inferType x
    if ← Meta.isProp xty then
      return (← mkAppM ``PLift #[xty], ← `(term| ⟨$(mkIdent a)⟩))
    else
      return (xty, mkIdent a)
  | (x, a) :: xs => do
    let (xsty, patt) ← defaultMkCtorProxyType xs
    let xty ← inferType x
    if ← Meta.isProp xty then
      withLocalDeclD `x' (← mkAppM ``PLift #[xty]) fun x' => do
        let xsty' := xsty.replaceFVar x (← mkAppM ``PLift.down #[x'])
        let ty ← decorateSigma (← mkAppM ``Sigma #[← mkLambdaFVars #[x'] xsty'])
        return (ty, ← `(term| ⟨⟨$(mkIdent a)⟩, $patt⟩))
    else
      let ty ← decorateSigma (← mkAppM ``Sigma #[← mkLambdaFVars #[x] xsty])
      return (ty, ← `(term| ⟨$(mkIdent a), $patt⟩))
def defaultMkProxyType (ctors : Array (Name × Expr × Term))
    (decorateSum : Expr → TermElabM Expr := pure) :
    TermElabM (Expr × Array Term × TSyntax `tactic) := do
  let mut types := #[]
  let mut patts := #[]
  for i in [0:ctors.size] do
    let (_ctorName, ty, patt) := ctors[i]!
    types := types.push ty
    patts := patts.push <| ← wrapSumAccess i ctors.size patt
  let (type, pf) ← mkCType types.toList
  return (type, patts, pf)
where
  mkCType (ctypes : List Expr) : TermElabM (Expr × TSyntax `tactic) :=
    match ctypes with
    | [] => return (mkConst ``Empty, ← `(tactic| cases x))
    | [x] => return (x, ← `(tactic| rfl))
    | x :: xs => do
      let (ty, pf) ← mkCType xs
      let pf ← `(tactic| cases x with | inl _ => rfl | inr x => $pf:tactic)
      return (← decorateSum (← mkAppM ``Sum #[x, ty]), pf)
  wrapSumAccess (cidx nctors : Nat) (spatt : Term) : TermElabM Term :=
    match cidx with
    | 0 =>
      if nctors = 1 then
        return spatt
      else
        `(term| Sum.inl $spatt)
    | cidx' + 1 => do
      let spatt ← wrapSumAccess cidx' (nctors - 1) spatt
      `(term| Sum.inr $spatt)
def ProxyEquivConfig.default (indVal : InductiveVal) : ProxyEquivConfig where
  proxyName := indVal.name.mkStr "proxyType"
  proxyEquivName := indVal.name.mkStr "proxyTypeEquiv"
  mkCtorProxyType := defaultMkCtorProxyType
  mkProxyType := defaultMkProxyType
def ensureProxyEquiv (config : ProxyEquivConfig) (indVal : InductiveVal) : TermElabM Unit := do
  if indVal.isRec then
    throwError
      "proxy equivalence: recursive inductive types are not supported (and are usually infinite)"
  if 0 < indVal.numIndices then
    throwError "proxy equivalence: inductive indices are not supported"
  let levels := indVal.levelParams.map Level.param
  forallBoundedTelescope indVal.type indVal.numParams fun params _sort => do
    let mut cdata := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← inferType <| mkAppN (mkConst ctorName levels) params
      cdata := cdata.push <| ←
        forallBoundedTelescope ctorType ctorInfo.numFields fun xs _itype => do
          let names ← xs.mapM (fun _ => mkFreshUserName `a)
          let (ty, ppatt) ← config.mkCtorProxyType (xs.zip names).toList
          let places := mkArray ctorInfo.numParams (← `(term| _))
          let argNames := names.map mkIdent
          let cpatt ← `(term| @$(mkIdent ctorName) $places* $argNames*)
          return (ctorName, ty, ppatt, cpatt)
    let (ctype, ppatts, pf) ← config.mkProxyType <|
      cdata.map (fun (ctorName, ty, ppatt, _) => (ctorName, ty, ppatt))
    let mut toFunAlts := #[]
    let mut invFunAlts := #[]
    for ppatt in ppatts, (_, _, _, cpatt) in cdata do
      toFunAlts := toFunAlts.push <| ← `(matchAltExpr| | $ppatt => $cpatt)
      invFunAlts := invFunAlts.push <| ← `(matchAltExpr| | $cpatt => $ppatt)
    trace[Elab.ProxyType] "proxy type: {ctype}"
    let ctype' ← mkLambdaFVars params ctype
    if let some const := (← getEnv).find? config.proxyName then
      unless ← isDefEq const.value! ctype' do
        throwError "Declaration {config.proxyName} already exists and it is not the proxy type."
      trace[Elab.ProxyType] "proxy type already exists"
    else
      addAndCompile <| Declaration.defnDecl
        { name := config.proxyName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType ctype'
          value := ctype' }
      setReducibleAttribute config.proxyName
      setProtected config.proxyName
      addDocString config.proxyName s!"A \"proxy type\" equivalent to `{indVal.name}` that is \
        constructed from `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum`. \
        See `{config.proxyEquivName}` for the equivalence. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyName}"
    let equivType ← mkAppM ``Equiv #[ctype, mkAppN (mkConst indVal.name levels) params]
    if let some const := (← getEnv).find? config.proxyEquivName then
      unless ← isDefEq const.type (← mkForallFVars params equivType) do
        throwError "Declaration {config.proxyEquivName} already exists and has the wrong type."
      trace[Elab.ProxyType] "proxy equivalence already exists"
    else
      trace[Elab.ProxyType] "constructing proxy equivalence"
      let mut toFun ← `(term| fun $toFunAlts:matchAlt*)
      let mut invFun ← `(term| fun $invFunAlts:matchAlt*)
      if indVal.numCtors == 0 then
        toFun ← `(term| fun x => nomatch x)
        invFun ← `(term| fun x => nomatch x)
      let equivBody ← `(term| { toFun := $toFun,
                                invFun := $invFun,
                                right_inv := by intro x; cases x <;> rfl
                                left_inv := by intro x; $pf:tactic })
      let equiv ← Term.elabTerm equivBody equivType
      Term.synthesizeSyntheticMVarsNoPostponing
      trace[Elab.ProxyType] "elaborated equivalence{indentExpr equiv}"
      let equiv' ← mkLambdaFVars params (← instantiateMVars equiv)
      addAndCompile <| Declaration.defnDecl
        { name := config.proxyEquivName
          levelParams := indVal.levelParams
          safety := DefinitionSafety.safe
          hints := ReducibilityHints.abbrev
          type := ← inferType equiv'
          value := equiv' }
      setProtected config.proxyEquivName
      addDocString config.proxyEquivName s!"An equivalence between the \"proxy type\" \
        `{config.proxyName}` and `{indVal.name}`. The proxy type is a reducible definition \
        that represents the inductive type using `Unit`, `PLift`, `Sigma`, `Empty`, and `Sum` \
        (and whatever other inductive types appear within the inductive type), and the \
        intended use is to define typeclass instances uses pre-existing instances on these. \
        (Generated by the `proxy_equiv%` elaborator.)"
      trace[Elab.ProxyType] "defined {config.proxyEquivName}"
def elabProxyEquiv (type : Term) (expectedType? : Option Expr) :
    TermElabM (Expr × InductiveVal) := do
  let type ← Term.elabType type
  if let some expectedType := expectedType? then
    let equivType ← Term.elabType (← `(_ ≃ $(← Term.exprToSyntax type)))
    unless ← isDefEq expectedType equivType do
      throwError
        "Could not unify expected type{indentExpr expectedType}\nwith{indentExpr equivType}"
  let type ← Term.tryPostponeIfHasMVars type "In proxy_equiv% elaborator"
  let type ← whnf type
  let .const declName _ := type.getAppFn
    | throwError "{type} is not a constant or constant application"
  return (type, ← getConstInfoInduct declName)
syntax (name := proxy_equiv) "proxy_equiv% " term : term
@[term_elab proxy_equiv]
def elab_proxy_equiv : Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(proxy_equiv% $t) => do
    let (type, indVal) ← elabProxyEquiv t expectedType?
    let config : ProxyEquivConfig := ProxyEquivConfig.default indVal
    ensureProxyEquiv config indVal
    mkAppOptM config.proxyEquivName (type.getAppArgs.map .some)
  | _ => throwUnsupportedSyntax
end Mathlib.ProxyType