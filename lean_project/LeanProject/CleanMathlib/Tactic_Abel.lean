import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.TryThis
import Mathlib.Util.AtomM
assert_not_exists OrderedAddCommMonoid
assert_not_exists TopologicalSpace
assert_not_exists PseudoMetricSpace
namespace Mathlib.Tactic.Abel
open Lean Elab Meta Tactic Qq
initialize registerTraceClass `abel
initialize registerTraceClass `abel.detail
structure Context where
  α       : Expr
  univ    : Level
  α0      : Expr
  isGroup : Bool
  inst    : Expr
def mkContext (e : Expr) : MetaM Context := do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | some cg => return ⟨α, u, α0, true, cg⟩
  | _ => return ⟨α, u, α0, false, c⟩
abbrev M := ReaderT Context AtomM
def Context.app (c : Context) (n : Name) (inst : Expr) : Array Expr → Expr :=
  mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)
def Context.mkApp (c : Context) (n inst : Name) (l : Array Expr) : MetaM Expr := do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l
def addG : Name → Name
  | .str p s => .str p (s ++ "g")
  | n => n
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs
def term {α} [AddCommMonoid α] (n : ℕ) (x a : α) : α := n • x + a
def termg {α} [AddCommGroup α] (n : ℤ) (x a : α) : α := n • x + a
def mkTerm (n x a : Expr) : M Expr := iapp ``term #[n, x, a]
def intToExpr (n : ℤ) : M Expr := do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n
inductive NormalExpr : Type
  | zero (e : Expr) : NormalExpr
  | nterm (e : Expr) (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : NormalExpr
  deriving Inhabited
def NormalExpr.e : NormalExpr → Expr
  | .zero e => e
  | .nterm e .. => e
instance : Coe NormalExpr Expr where coe := NormalExpr.e
def NormalExpr.term' (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : M NormalExpr :=
  return .nterm (← mkTerm n.1 x.2 a) n x a
def NormalExpr.zero' : M NormalExpr := return NormalExpr.zero (← read).α0
open NormalExpr
theorem const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') :
    k + @term α _ n x a = term n x a' := by
  simp [h.symm, term, add_comm, add_assoc]
theorem const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') :
    k + @termg α _ n x a = termg n x a' := by
  simp [h.symm, termg, add_comm, add_assoc]
theorem term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') :
    @term α _ n x a + k = term n x a' := by
  simp [h.symm, term, add_assoc]
theorem term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') :
    @termg α _ n x a + k = termg n x a' := by
  simp [h.symm, termg, add_assoc]
theorem term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
    (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]
theorem term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
    (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  simp only [termg, h₁.symm, add_zsmul, h₂.symm]
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂
theorem zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a := by
  simp [term, zero_nsmul, one_nsmul]
theorem zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a := by
  simp [termg, zero_zsmul]
partial def evalAdd : NormalExpr → NormalExpr → M (NormalExpr × Expr)
  | zero _, e₂ => do
    let p ← mkAppM ``zero_add #[e₂]
    return (e₂, p)
  | e₁, zero _ => do
    let p ← mkAppM ``add_zero #[e₁]
    return (e₁, p)
  | he₁@(nterm e₁ n₁ x₁ a₁), he₂@(nterm e₂ n₂ x₂ a₂) => do
    if x₁.1 = x₂.1 then
      let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HAdd.hAdd #[n₁.1, n₂.1])
      let (a', h₂) ← evalAdd a₁ a₂
      let k := n₁.2 + n₂.2
      let p₁ ← iapp ``term_add_term
        #[n₁.1, x₁.2, a₁, n₂.1, a₂, n'.expr, a', ← n'.getProof, h₂]
      if k = 0 then do
        let p ← mkEqTrans p₁ (← iapp ``zero_term #[x₁.2, a'])
        return (a', p)
      else return (← term' (n'.expr, k) x₁ a', p₁)
    else if x₁.1 < x₂.1 then do
      let (a', h) ← evalAdd a₁ he₂
      return (← term' n₁ x₁ a', ← iapp ``term_add_const #[n₁.1, x₁.2, a₁, e₂, a', h])
    else do
      let (a', h) ← evalAdd he₁ a₂
      return (← term' n₂ x₂ a', ← iapp ``const_add_term #[e₁, n₂.1, x₂.2, a₂, a', h])
theorem term_neg {α} [AddCommGroup α] (n x a n' a')
    (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a' := by
  simpa [h₂.symm, h₁.symm, termg] using add_comm _ _
def evalNeg : NormalExpr → M (NormalExpr × Expr)
  | (zero _) => do
    let p ← (← read).mkApp ``neg_zero ``NegZeroClass #[]
    return (← zero', p)
  | (nterm _ n x a) => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``Neg.neg #[n.1])
    let (a', h₂) ← evalNeg a
    return (← term' (n'.expr, -n.2) x a',
      (← read).app ``term_neg (← read).inst #[n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])
def smul {α} [AddCommMonoid α] (n : ℕ) (x : α) : α := n • x
def smulg {α} [AddCommGroup α] (n : ℤ) (x : α) : α := n • x
theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
  simp [smul, nsmul_zero]
theorem zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0 := by
  simp [smulg, zsmul_zero]
theorem term_smul {α} [AddCommMonoid α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smul c a = a') :
    smul c (@term α _ n x a) = term n' x a' := by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']
theorem term_smulg {α} [AddCommGroup α] (c n x a n' a')
    (h₁ : c * n = n') (h₂ : smulg c a = a') :
    smulg c (@termg α _ n x a) = termg n' x a' := by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]
def evalSMul (k : Expr × ℤ) : NormalExpr → M (NormalExpr × Expr)
  | zero _ => return (← zero', ← iapp ``zero_smul #[k.1])
  | nterm _ n x a => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HMul.hMul #[k.1, n.1])
    let (a', h₂) ← evalSMul k a
    return (← term' (n'.expr, k.2 * n.2) x a',
      ← iapp ``term_smul #[k.1, n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])
theorem term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0 := by simp [term]
theorem term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0 := by simp [termg]
theorem term_atom_pf {α} [AddCommMonoid α] (x x' : α) (h : x = x') : x = term 1 x' 0 := by
  simp [term, h]
theorem term_atom_pfg {α} [AddCommGroup α] (x x' : α) (h : x = x') : x = termg 1 x' 0 := by
  simp [termg, h]
def evalAtom (e : Expr) : M (NormalExpr × Expr) := do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let (i, a) ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, a, p]
  return (← term' (← intToExpr 1, 1) (i, a) (← zero'), p)
theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg, h]
theorem unfold_smul {α} [AddCommMonoid α] (n) (x y : α)
    (h : smul n x = y) : n • x = y := h
theorem unfold_smulg {α} [AddCommGroup α] (n : ℕ) (x y : α)
    (h : smulg (Int.ofNat n) x = y) : (n : ℤ) • x = y := h
theorem unfold_zsmul {α} [AddCommGroup α] (n : ℤ) (x y : α)
    (h : smulg n x = y) : n • x = y := h
lemma subst_into_smul {α} [AddCommMonoid α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smul α _ tl tr = t) : smul l r = t := by simp [prl, prr, prt]
lemma subst_into_smulg {α} [AddCommGroup α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smulg α _ tl tr = t) : smulg l r = t := by simp [prl, prr, prt]
lemma subst_into_smul_upcast {α} [AddCommGroup α]
    (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
    (prt : @smulg α _ zl tr = t) : smul l r = t := by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, natCast_zsmul]
lemma subst_into_add {α} [AddCommMonoid α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
lemma subst_into_addg {α} [AddCommGroup α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
lemma subst_into_negg {α} [AddCommGroup α] (a ta t : α)
    (pra : a = ta) (prt : -ta = t) : -a = t := by
  simp [pra, prt]
def evalSMul' (eval : Expr → M (NormalExpr × Expr))
    (is_smulg : Bool) (orig e₁ e₂ : Expr) : M (NormalExpr × Expr) := do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Meta.NormNum.eval e₁ catch _ => pure { expr := e₁ }
  let p₁ ← p₁.getDM (mkEqRefl e₁')
  match e₁'.int? with
  | some n => do
    let c ← read
    let (e₂', p₂) ← eval e₂
    if c.isGroup = is_smulg then do
      let (e', p) ← evalSMul (e₁', n) e₂'
      return (e', ← iapp ``subst_into_smul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p])
    else do
      if ¬ c.isGroup then throwError "Doesn't make sense to us `smulg` in a monoid. "
      let zl ← Expr.ofInt q(ℤ) n
      let p₁' ← mkEqRefl zl
      let (e', p) ← evalSMul (zl, n) e₂'
      return (e', c.app ``subst_into_smul_upcast c.inst #[e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none => evalAtom orig
partial def eval (e : Expr) : M (NormalExpr × Expr) := do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    return (e', ← iapp ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p'])
  | (``HSub.hSub, #[_, _, _ ,_, e₁, e₂]) => do
    let e₂' ← mkAppM ``Neg.neg #[e₂]
    let e ← mkAppM ``HAdd.hAdd #[e₁, e₂']
    let (e', p) ← eval e
    let p' ← (← read).mkApp ``unfold_sub ``SubtractionMonoid #[e₁, e₂, e', p]
    return (e', p')
  | (``Neg.neg, #[_, _, e]) => do
    let (e₁, p₁) ← eval e
    let (e₂, p₂) ← evalNeg e₁
    return (e₂, ← iapp `Mathlib.Tactic.Abel.subst_into_neg #[e, e₁, e₂, p₁, p₂])
  | (``AddMonoid.nsmul, #[_, _, e₁, e₂]) => do
    let n ← if (← read).isGroup then mkAppM ``Int.ofNat #[e₁] else pure e₁
    let (e', p) ← eval <| ← iapp ``smul #[n, e₂]
    return (e', ← iapp ``unfold_smul #[e₁, e₂, e', p])
  | (``SubNegMonoid.zsmul, #[_, _, e₁, e₂]) => do
      if ¬ (← read).isGroup then failure
      let (e', p) ← eval <| ← iapp ``smul #[e₁, e₂]
      return (e', (← read).app ``unfold_zsmul (← read).inst #[e₁, e₂, e', p])
  | (``SMul.smul, #[.const ``Int _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``SMul.smul, #[.const ``Nat _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Int _, _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Nat _, _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``smul, #[_, _, e₁, e₂]) => evalSMul' eval false e e₁ e₂
  | (``smulg, #[_, _, e₁, e₂]) => evalSMul' eval true e e₁ e₂
  | (``OfNat.ofNat, #[_, .lit (.natVal 0), _])
  | (``Zero.zero, #[_, _]) =>
    if ← isDefEq e (← read).α0 then
      pure (← zero', ← mkEqRefl (← read).α0)
    else
      evalAtom e
  | _ => evalAtom e
syntax (name := abel1) "abel1" "!"? : tactic
open Lean Elab Meta Tactic
elab_rules : tactic | `(tactic| abel1 $[!%$tk]?) => withMainContext do
  let tm := if tk.isSome then .default else .reducible
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "abel1 requires an equality goal"
  trace[abel] "running on an equality `{e₁} = {e₂}`."
  let c ← mkContext e₁
  closeMainGoal `abel1 <| ← AtomM.run tm <| ReaderT.run (r := c) do
    let (e₁', p₁) ← eval e₁
    trace[abel] "found `{p₁}`, a proof that `{e₁} = {e₁'.e}`"
    let (e₂', p₂) ← eval e₂
    trace[abel] "found `{p₂}`, a proof that `{e₂} = {e₂'.e}`"
    unless ← isDefEq e₁' e₂' do
      throwError "abel1 found that the two sides were not equal"
    trace[abel] "verified that the simplified forms are identical"
    mkEqTrans p₁ (← mkEqSymm p₂)
@[inherit_doc abel1] macro (name := abel1!) "abel1!" : tactic => `(tactic| abel1 !)
theorem term_eq {α : Type*} [AddCommMonoid α] (n : ℕ) (x a : α) : term n x a = n • x + a := rfl
theorem termg_eq {α : Type*} [AddCommGroup α] (n : ℤ) (x a : α) : termg n x a = n • x + a := rfl
def NormalExpr.isAtom : NormalExpr → Bool
  | .nterm _ (_, 1) _ (.zero _) => true
  | _ => false
inductive AbelMode where
  | term
  | raw
structure AbelNF.Config where
  red := TransparencyMode.reducible
  recursive := true
  mode := AbelMode.term
declare_config_elab elabAbelNFConfig AbelNF.Config
partial def abelNFCore
    (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}])
    (congrTheorems := ← getSimpCongrTheorems)
  let simp ← match cfg.mode with
  | .raw => pure pure
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx' := ctx.setSimpTheorems #[← thms.foldlM (·.addConst ·) {:_}]
    pure fun r' : Simp.Result ↦ do
      r'.mkEqTrans (← Simp.main r'.expr ctx' (methods := ← Lean.Meta.Simp.mkDefaultMethods)).1
  let rec
    go root parent :=
      let pre : Simp.Simproc := fun e =>
        try
          guard <| root || parent != e 
          let e ← withReducible <| whnf e
          guard e.isApp 
          let (a, pa) ← eval e (← mkContext e) { red := cfg.red, evalAtom } s
          guard !a.isAtom
          let r ← simp { expr := a, proof? := pa }
          if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
          pure (.done r)
        catch _ => pure <| .continue
      let post : Simp.Simproc := Simp.postDefault #[]
      (·.1) <$> Simp.main parent ctx (methods := { pre, post }),
    evalAtom := if cfg.recursive then go false else fun e ↦ pure { expr := e }
  go true e
open Elab.Tactic Parser.Tactic
def abelNFTarget (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← withReducible goal.getType'
  let r ← abelNFCore s cfg tgt
  if r.expr.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    if r.expr == tgt then throwError "abel_nf made no progress"
    replaceMainGoal [← applySimpResultToTarget goal tgt r]
def abelNFLocalDecl (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← abelNFCore s cfg tgt
  if myres.expr == tgt then throwError "abel_nf made no progress"
  match ← applySimpResultToLocalDecl goal fvarId myres false with
  | none => replaceMainGoal []
  | some (_, newGoal) => replaceMainGoal [newGoal]
syntax (name := abel_term) "abel" (&" raw" <|> &" term")? (location)? : tactic
syntax (name := abel!_term) "abel!" (&" raw" <|> &" term")? (location)? : tactic
elab (name := abelNF) "abel_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  withLocation loc (abelNFLocalDecl s cfg) (abelNFTarget s cfg)
    fun _ ↦ throwError "abel_nf made no progress"
@[inherit_doc abelNF] macro "abel_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| abel_nf ! $cfg:optConfig $(loc)?)
@[inherit_doc abelNF] syntax (name := abelNFConv) "abel_nf" "!"? optConfig : conv
@[tactic abelNFConv] def elabAbelNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default }
    Conv.applySimpResult (← abelNFCore (← IO.mkRef {}) cfg (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax
@[inherit_doc abelNF] macro "abel_nf!" cfg:optConfig : conv => `(conv| abel_nf ! $cfg:optConfig)
macro (name := abel) "abel" : tactic =>
  `(tactic| first | abel1 | try_this abel_nf)
@[inherit_doc abel] macro "abel!" : tactic =>
  `(tactic| first | abel1! | try_this abel_nf!)
macro (name := abelConv) "abel" : conv =>
  `(conv| first | discharge => abel1 | try_this abel_nf)
@[inherit_doc abelConv] macro "abel!" : conv =>
  `(conv| first | discharge => abel1! | try_this abel_nf!)
end Mathlib.Tactic.Abel