import Lean.Elab.BuiltinCommand
import Lean.Elab.MacroArgUtil
import Mathlib.Lean.Elab.Term
import Mathlib.Lean.PrettyPrinter.Delaborator
import Mathlib.Tactic.ScopedNS
import Batteries.Linter.UnreachableTactic
import Batteries.Util.ExtendedBinder
import Batteries.Lean.Syntax
namespace Mathlib.Notation3
open Lean Parser Meta Elab Command PrettyPrinter.Delaborator SubExpr
open Batteries.ExtendedBinder
initialize registerTraceClass `notation3
syntax "expand_binders% " "(" ident " => " term ")" extBinders ", " term : term
macro_rules
  | `(expand_binders% ($x => $term) $y:extBinder, $res) =>
    `(expand_binders% ($x => $term) ($y:extBinder), $res)
  | `(expand_binders% ($_ => $_), $res) => pure res
macro_rules
  | `(expand_binders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident : $ty ↦ expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) (_%$ph $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun _%$ph : $ty ↦ expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident ↦ expand_binders% ($x => $term) (h : satisfies_binder_pred% $y $pred)
        $[$binders]*, $res)
macro (name := expandFoldl) "expand_foldl% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg ↦ do
    term.replaceM fun e ↦
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expand_foldr% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res ↦ do
    term.replaceM fun e ↦
      return if e == x then some arg else if e == y then some res else none
syntax foldKind := &"foldl" <|> &"foldr"
syntax bindersItem := atomic("(" "..." ")")
syntax foldAction := "(" ident ppSpace strLit "*" (precedence)? " => " foldKind
  " (" ident ppSpace ident " => " term ") " term ")"
syntax identOptScoped :=
  ident (notFollowedBy(":" "(" "scoped") precedence)? (":" "(" "scoped " ident " => " term ")")?
syntax notation3Item := strLit <|> bindersItem <|> identOptScoped <|> foldAction
structure MatchState where
  vars : Std.HashMap Name (SubExpr × LocalContext × LocalInstances)
  scopeState : Option (Array (TSyntax ``extBinderParenthesized))
  foldState : Std.HashMap Name (Array Term)
def Matcher := MatchState → DelabM MatchState
  deriving Inhabited
def MatchState.empty : MatchState where
  vars := {}
  scopeState := none
  foldState := {}
def MatchState.withVar {α : Type} (s : MatchState) (name : Name)
    (m : DelabM α) : DelabM α := do
  let some (se, lctx, linsts) := s.vars[name]? | failure
  withLCtx lctx linsts <| withTheReader SubExpr (fun _ => se) <| m
def MatchState.delabVar (s : MatchState) (name : Name) (checkNot? : Option Expr := none) :
    DelabM Term :=
  s.withVar name do
    if let some checkNot := checkNot? then
      guard <| checkNot != (← getExpr)
    delab
def MatchState.captureSubexpr (s : MatchState) (name : Name) : DelabM MatchState := do
  return {s with vars := s.vars.insert name (← readThe SubExpr, ← getLCtx, ← getLocalInstances)}
def MatchState.getFoldArray (s : MatchState) (name : Name) : Array Term :=
  s.foldState[name]?.getD #[]
def MatchState.getBinders (s : MatchState) : Array (TSyntax ``extBinderParenthesized) :=
  s.scopeState.getD #[]
def MatchState.pushFold (s : MatchState) (name : Name) (t : Term) : MatchState :=
  let ts := (s.getFoldArray name).push t
  {s with foldState := s.foldState.insert name ts}
def matchVar (c : Name) : Matcher := fun s => do
  if let some (se, _, _) := s.vars[c]? then
    guard <| se.expr == (← getExpr)
    return s
  else
    s.captureSubexpr c
def matchExpr (p : Expr → Bool) : Matcher := fun s => do
  guard <| p (← getExpr)
  return s
def matchFVar (userName : Name) (matchTy : Matcher) : Matcher := fun s => do
  let .fvar fvarId ← getExpr | failure
  guard <| userName == (← fvarId.getUserName)
  withType (matchTy s)
def matchTypeOf (matchTy : Matcher) : Matcher := fun s => do
  withType (matchTy s)
def natLitMatcher (n : Nat) : Matcher := fun s => do
  guard <| (← getExpr).rawNatLit? == n
  return s
def matchApp (matchFun matchArg : Matcher) : Matcher := fun s => do
  guard <| (← getExpr).isApp
  let s ← withAppFn <| matchFun s
  let s ← withAppArg <| matchArg s
  return s
def matchForall (matchDom : Matcher) (matchBody : Expr → Matcher) : Matcher := fun s => do
  guard <| (← getExpr).isForall
  let s ← withBindingDomain <| matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s
def matchLambda (matchDom : Matcher) (matchBody : Expr → Matcher) : Matcher := fun s => do
  guard <| (← getExpr).isLambda
  let s ← withBindingDomain <| matchDom s
  let s ← withBindingBodyUnusedName' fun _ arg => matchBody arg s
  return s
def setupLCtx (lctx : LocalContext) (boundNames : Array Name) :
    MetaM (LocalContext × Std.HashMap FVarId Name) := do
  let mut lctx := lctx
  let mut boundFVars := {}
  for name in boundNames do
    let fvarId ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fvarId name (← withLCtx lctx (← getLocalInstances) mkFreshTypeMVar)
    boundFVars := boundFVars.insert fvarId name
  return (lctx, boundFVars)
partial def exprToMatcher (boundFVars : Std.HashMap FVarId Name)
    (localFVars : Std.HashMap FVarId Term) (e : Expr) :
    OptionT TermElabM (List Name × Term) := do
  match e with
  | .mvar .. => return ([], ← `(pure))
  | .const n _ => return ([`app ++ n], ← ``(matchExpr (Expr.isConstOf · $(quote n))))
  | .sort .. => return ([`sort], ← ``(matchExpr Expr.isSort))
  | .fvar fvarId =>
    if let some n := boundFVars[fvarId]? then
      return ([], ← ``(matchVar $(quote n)))
    else if let some s := localFVars[fvarId]? then
      return ([], ← ``(matchExpr (· == $s)))
    else
      let n ← fvarId.getUserName
      if n.hasMacroScopes then
        let (_, m) ← exprToMatcher boundFVars localFVars (← instantiateMVars (← inferType e))
        return ([`fvar], ← ``(matchTypeOf $m))
      else
        let (_, m) ← exprToMatcher boundFVars localFVars (← instantiateMVars (← inferType e))
        return ([`fvar], ← ``(matchFVar $(quote n) $m))
  | .app .. =>
    e.withApp fun f args => do
      let (keys, matchF) ← exprToMatcher boundFVars localFVars f
      let mut fty ← inferType f
      let mut matcher := matchF
      for arg in args do
        fty ← whnf fty
        guard fty.isForall
        let bi := fty.bindingInfo!
        fty := fty.bindingBody!.instantiate1 arg
        if bi.isInstImplicit then
          matcher ← ``(matchApp $matcher pure)
        else
          let (_, matchArg) ← exprToMatcher boundFVars localFVars arg
          matcher ← ``(matchApp $matcher $matchArg)
      return (if keys.isEmpty then [`app] else keys, matcher)
  | .lit (.natVal n) => return ([`lit], ← ``(natLitMatcher $(quote n)))
  | .forallE n t b bi =>
    let (_, matchDom) ← exprToMatcher boundFVars localFVars t
    withLocalDecl n bi t fun arg => withFreshMacroScope do
      let n' ← `(n)
      let body := b.instantiate1 arg
      let localFVars' := localFVars.insert arg.fvarId! n'
      let (_, matchBody) ← exprToMatcher boundFVars localFVars' body
      return ([`forallE], ← ``(matchForall $matchDom (fun $n' => $matchBody)))
  | .lam n t b bi =>
    let (_, matchDom) ← exprToMatcher boundFVars localFVars t
    withLocalDecl n bi t fun arg => withFreshMacroScope do
      let n' ← `(n)
      let body := b.instantiate1 arg
      let localFVars' := localFVars.insert arg.fvarId! n'
      let (_, matchBody) ← exprToMatcher boundFVars localFVars' body
      return ([`lam], ← ``(matchLambda $matchDom (fun $n' => $matchBody)))
  | _ =>
    trace[notation3] "can't generate matcher for {e}"
    failure
partial def mkExprMatcher (stx : Term) (boundNames : Array Name) :
    OptionT TermElabM (List Name × Term) := do
  let (lctx, boundFVars) ← setupLCtx (← getLCtx) boundNames
  withLCtx lctx (← getLocalInstances) do
    let patt ←
      try
        Term.elabPattern stx none
      catch e =>
        logException e
        trace[notation3] "Could not elaborate pattern{indentD stx}\nError: {e.toMessageData}"
        failure
    trace[notation3] "Generating matcher for pattern {patt}"
    exprToMatcher boundFVars {} patt
partial def matchScoped (lit scopeId : Name) (smatcher : Matcher) : Matcher := go #[] where
  go (binders : Array (TSyntax ``extBinderParenthesized)) : Matcher := fun s => do
    s.withVar lit do
    try
      let s ← smatcher {s with vars := s.vars.erase scopeId}
      s.withVar scopeId do
        guard (← getExpr).isLambda
        let prop ← try Meta.isProp (← getExpr).bindingDomain! catch _ => pure false
        let isDep := (← getExpr).bindingBody!.hasLooseBVar 0
        let ppTypes ← getPPOption getPPPiBinderTypes 
        let dom ← withBindingDomain delab
        withBindingBodyUnusedName fun x => do
          let x : Ident := ⟨x⟩
          let binder ←
            if prop && !isDep then
              `(extBinderParenthesized|(_ : $dom))
            else if prop || ppTypes then
              `(extBinderParenthesized|($x:ident : $dom))
            else
              `(extBinderParenthesized|($x:ident))
          let s ← s.captureSubexpr lit
          let binders := binders.push binder
          go binders s
    catch _ =>
      guard <| !binders.isEmpty
      if let some binders₂ := s.scopeState then
        guard <| binders == binders₂ 
        return s
      else
        return {s with scopeState := binders}
partial def mkScopedMatcher (lit scopeId : Name) (scopedTerm : Term) (boundNames : Array Name) :
    OptionT TermElabM (List Name × Term) := do
  let (keys, smatcher) ← mkExprMatcher scopedTerm (boundNames.push scopeId)
  return (keys, ← ``(matchScoped $(quote lit) $(quote scopeId) $smatcher))
partial def matchFoldl (lit x y : Name) (smatcher : Matcher) (sinit : Matcher) :
    Matcher := fun s => do
  s.withVar lit do
    let expr ← getExpr
    let s := {s with vars := s.vars |>.erase x |>.erase y}
    let some s ← try some <$> smatcher s catch _ => pure none
      | 
        sinit s
    let s := s.pushFold lit (← s.delabVar y expr)
    let some newLit := s.vars[x]? | failure
    if newLit.1.expr == expr then failure
    let s := {s with vars := s.vars.insert lit newLit}
    matchFoldl lit x y smatcher sinit s
partial def mkFoldlMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name) :
    OptionT TermElabM (List Name × Term) := do
  let boundNames' := boundNames |>.push x |>.push y
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote x) $(quote y) $smatcher $sinit))
partial def mkFoldrMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : Array Name) :
    OptionT TermElabM (List Name × Term) := do
  let boundNames' := boundNames |>.push x |>.push y
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote y) $(quote x) $smatcher $sinit))
def mkNameFromSyntax (name? : Option (TSyntax ``namedName))
    (syntaxArgs : Array (TSyntax `stx)) (attrKind : TSyntax ``Term.attrKind) :
    CommandElabM Name := do
  if let some name := name? then
    match name with
    | `(namedName| (name := $n)) => return n.getId
    | _ => pure ()
  let name ← liftMacroM <| mkNameFromParserSyntax `term (mkNullNode syntaxArgs)
  addMacroScopeIfLocal name attrKind
inductive BoundValueType
  | normal
  | foldl
  | foldr
syntax prettyPrintOpt := "(" &"prettyPrint" " := " (&"true" <|> &"false") ")"
def getPrettyPrintOpt (opt? : Option (TSyntax ``prettyPrintOpt)) : Bool :=
  if let some opt := opt? then
    match opt with
    | `(prettyPrintOpt| (prettyPrint := false)) => false
    | _ => true
  else
    true
elab (name := notation3) doc:(docComment)? attrs?:(Parser.Term.attributes)? attrKind:Term.attrKind
    "notation3" prec?:(precedence)? name?:(namedName)? prio?:(namedPrio)?
    pp?:(ppSpace prettyPrintOpt)? items:(ppSpace notation3Item)+ " => " val:term : command => do
  let mut boundIdents : Std.HashMap Name Ident := {}
  let mut boundValues : Std.HashMap Name Syntax := {}
  let mut boundNames : Array Name := #[]
  let mut boundType : Std.HashMap Name BoundValueType := {}
  let pushMacro (syntaxArgs : Array (TSyntax `stx)) (pattArgs : Array Syntax)
      (mac : TSyntax ``macroArg) := do
    let (syntaxArg, pattArg) ← expandMacroArg mac
    return (syntaxArgs.push syntaxArg, pattArgs.push pattArg)
  let mut syntaxArgs := #[]
  let mut pattArgs := #[]
  let mut matchers := #[]
  let mut hasBindersItem := false
  let mut hasScoped := false
  for item in items do
    match item with
    | `(notation3Item| $lit:str) =>
      syntaxArgs := syntaxArgs.push (← `(stx| $lit:str))
      pattArgs := pattArgs.push <| mkAtomFrom lit lit.1.isStrLit?.get!
    | `(notation3Item| $_:bindersItem) =>
      if hasBindersItem then
        throwErrorAt item "Cannot have more than one `(...)` item."
      hasBindersItem := true
      if let `(stx| $lit:str) := syntaxArgs.back! then
        syntaxArgs := syntaxArgs.pop.push (← `(stx| $(quote lit.getString.trimRight):str))
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* $(prec?)? => $kind ($x $y => $scopedTerm) $init)) =>
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <| ←
        `(macroArg| $id:ident:sepBy(term $(prec?)?, $sep:str))
      let scopedTerm' ← scopedTerm.replaceM fun s => pure boundValues[s.getId]?
      let init' ← init.replaceM fun s => pure boundValues[s.getId]?
      boundIdents := boundIdents.insert id.getId id
      match kind with
        | `(foldKind| foldl) =>
          boundValues := boundValues.insert id.getId <| ←
            `(expand_foldl% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundNames := boundNames.push id.getId
          boundType := boundType.insert id.getId .foldl
          matchers := matchers.push <|
            mkFoldlMatcher id.getId x.getId y.getId scopedTerm init boundNames
        | `(foldKind| foldr) =>
          boundValues := boundValues.insert id.getId <| ←
            `(expand_foldr% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundNames := boundNames.push id.getId
          boundType := boundType.insert id.getId .foldr
          matchers := matchers.push <|
            mkFoldrMatcher id.getId x.getId y.getId scopedTerm init boundNames
        | _ => throwUnsupportedSyntax
    | `(notation3Item| $lit:ident $(prec?)? : (scoped $scopedId:ident => $scopedTerm)) =>
      hasScoped := true
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <|←
        `(macroArg| $lit:ident:term $(prec?)?)
      matchers := matchers.push <|
        mkScopedMatcher lit.getId scopedId.getId scopedTerm boundNames
      let scopedTerm' ← scopedTerm.replaceM fun s => pure boundValues[s.getId]?
      boundIdents := boundIdents.insert lit.getId lit
      boundValues := boundValues.insert lit.getId <| ←
        `(expand_binders% ($scopedId => $scopedTerm') $$binders:extBinders,
          $(⟨lit.1.mkAntiquotNode `term⟩):term)
      boundNames := boundNames.push lit.getId
    | `(notation3Item| $lit:ident $(prec?)?) =>
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <|←
        `(macroArg| $lit:ident:term $(prec?)?)
      boundIdents := boundIdents.insert lit.getId lit
      boundValues := boundValues.insert lit.getId <| lit.1.mkAntiquotNode `term
      boundNames := boundNames.push lit.getId
    | _stx => throwUnsupportedSyntax
  if hasScoped && !hasBindersItem then
    throwError "If there is a `scoped` item then there must be a `(...)` item for binders."
  let name ← mkNameFromSyntax name? syntaxArgs attrKind
  elabCommand <| ← `(command|
    $[$doc]? $(attrs?)? $attrKind
    syntax $(prec?)? (name := $(Lean.mkIdent name)) $(prio?)? $[$syntaxArgs]* : term)
  let currNamespace : Name ← getCurrNamespace
  let fullName := currNamespace ++ name
  trace[notation3] "syntax declaration has name {fullName}"
  let pat : Term := ⟨mkNode fullName pattArgs⟩
  let val' ← val.replaceM fun s => pure boundValues[s.getId]?
  let mut macroDecl ← `(macro_rules | `($pat) => `($val'))
  if isLocalAttrKind attrKind then
    macroDecl ← `(section set_option quotPrecheck.allowSectionVars true $macroDecl end)
  elabCommand macroDecl
  if getPrettyPrintOpt pp? then
    matchers := matchers.push <| Mathlib.Notation3.mkExprMatcher val boundNames
    let matchersM? := (matchers.reverse.mapM id).run
    let matchers? ← if isLocalAttrKind attrKind then
      runTermElabM fun _ => matchersM?
    else
      liftTermElabM matchersM?
    if let some ms := matchers? then
      trace[notation3] "Matcher creation succeeded; assembling delaborator"
      let delabName := name ++ `delab
      let matcher ← ms.foldrM (fun m t => `($(m.2) >=> $t)) (← `(pure))
      trace[notation3] "matcher:{indentD matcher}"
      let mut result ← `(`($pat))
      for (name, id) in boundIdents.toArray do
        match boundType.getD name .normal with
        | .normal => result ← `(MatchState.delabVar s $(quote name) (some e) >>= fun $id => $result)
        | .foldl => result ←
          `(let $id := (MatchState.getFoldArray s $(quote name)).reverse; $result)
        | .foldr => result ←
          `(let $id := MatchState.getFoldArray s $(quote name); $result)
      if hasBindersItem then
        result ← `(`(extBinders| $$(MatchState.getBinders s)*) >>= fun binders => $result)
      elabCommand <| ← `(command|
        def $(Lean.mkIdent delabName) : Delab := whenPPOption getPPNotation <|
          getExpr >>= fun e => $matcher MatchState.empty >>= fun s => $result)
      trace[notation3] "Defined delaborator {currNamespace ++ delabName}"
      let delabKeys := ms.foldr (·.1 ++ ·) []
      trace[notation3] "Adding `delab` attribute for keys {delabKeys}"
      for key in delabKeys do
        elabCommand <|
          ← `(command| attribute [$attrKind delab $(mkIdent key)] $(Lean.mkIdent delabName))
    else
      logWarning s!"\
        Was not able to generate a pretty printer for this notation. \
        If you do not expect it to be pretty printable, then you can use \
        `notation3 (prettyPrint := false)`. \
        If the notation expansion refers to section variables, be sure to do `local notation3`. \
        Otherwise, you might be able to adjust the notation expansion to make it matchable; \
        pretty printing relies on deriving an expression matcher from the expansion. \
        (Use `set_option trace.notation3 true` to get some debug information.)"
initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``«notation3»
macro_rules
  | `($[$doc]? $(attr)? scoped[$ns] notation3 $(prec)? $(n)? $(prio)? $(pp)? $items* => $t) =>
    `(with_weak_namespace $(mkIdentFrom ns <| rootNamespace ++ ns.getId)
      $[$doc]? $(attr)? scoped notation3 $(prec)? $(n)? $(prio)? $(pp)? $items* => $t)
end Notation3
end Mathlib