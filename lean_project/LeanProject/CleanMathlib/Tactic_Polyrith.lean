import Mathlib.Tactic.LinearCombination
namespace Mathlib.Tactic.Polyrith
open Lean
open Meta Ring Qq PrettyPrinter AtomM
initialize registerTraceClass `Meta.Tactic.polyrith
inductive Poly
  | const : ℚ → Poly
  | var : ℕ → Poly
  | hyp : Term → Poly
  | add : Poly → Poly → Poly
  | sub : Poly → Poly → Poly
  | mul : Poly → Poly → Poly
  | div : Poly → Poly → Poly
  | pow : Poly → Poly → Poly
  | neg : Poly → Poly
  deriving BEq, Repr
def Poly.format : Poly → Lean.Format
  | .const z => toString z
  | .var n => s!"var{n}"
  | .hyp e => s!"hyp{e}" 
  | .add p q => s!"({p.format} + {q.format})"
  | .sub p q => s!"({p.format} - {q.format})"
  | .mul p q => s!"({p.format} * {q.format})"
  | .div p q => s!"({p.format} / {q.format})" 
  | .pow p q => s!"({p.format} ^ {q.format})"
  | .neg p => s!"-{p.format}"
instance : Lean.ToFormat Poly := ⟨Poly.format⟩
instance : ToString Poly := ⟨(toString ·.format)⟩
instance : Repr Poly := ⟨fun p _ => p.format⟩
instance : Inhabited Poly := ⟨Poly.const 0⟩
instance : Quote ℤ where quote
  | .ofNat n => quote n
  | .negSucc n => Unhygienic.run `(-$(quote n))
instance : Quote ℚ where
  quote q :=
    if q.den = 1 then quote q.num
    else Unhygienic.run `($(quote q.num) / $(quote q.den))
variable (vars : Array Syntax.Term) in
def Poly.toSyntax : Poly → Unhygienic Syntax.Term
  | .const z => pure (quote z)
  | .var n => pure vars[n]!
  | .hyp stx => pure stx
  | .add p q => do `($(← p.toSyntax) + $(← q.toSyntax))
  | .sub p q => do `($(← p.toSyntax) - $(← q.toSyntax))
  | .mul p q => do `($(← p.toSyntax) * $(← q.toSyntax))
  | .div p q => do `($(← p.toSyntax) / $(← q.toSyntax))
  | .pow p q => do `($(← p.toSyntax) ^ $(← q.toSyntax))
  | .neg p => do `(-$(← p.toSyntax))
attribute [local instance] monadLiftOptionMetaM in
partial def parse {u : Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (c : Ring.Cache sα) (e : Q($α)) : AtomM Poly := do
  let els := do
    try pure <| Poly.const (← (← NormNum.derive e).toRat)
    catch _ => pure <| Poly.var (← addAtom e).1
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα with
  | ``HAdd.hAdd, _ | ``Add.add, _ => match e with
    | ~q($a + $b) => pure <| (← parse sα c a).add (← parse sα c b)
    | _ => els
  | ``HMul.hMul, _ | ``Mul.mul, _ => match e with
    | ~q($a * $b) => pure <| (← parse sα c a).mul (← parse sα c b)
    | _ => els
  | ``HSMul.hSMul, _ => match e with
    | ~q(($a : ℕ) • ($b : «$α»)) => pure <| (← parse sℕ .nat a).mul (← parse sα c b)
    | _ => els
  | ``HPow.hPow, _ | ``Pow.pow, _ => match e with
    | ~q($a ^ $b) =>
      try pure <| (← parse sα c a).pow (.const (← (← NormNum.derive (u := .zero) b).toRat))
      catch _ => els
    | _ => els
  | ``Neg.neg, some _ => match e with
    | ~q(-$a) => pure <| (← parse sα c a).neg
  | ``HSub.hSub, some _ | ``Sub.sub, some _ => match e with
    | ~q($a - $b) => pure <| (← parse sα c a).sub (← parse sα c b)
    | _ => els
  | _, _ => els
inductive Source where
  | input : Nat → Source
  | fvar : FVarId → Source
def parseContext (only : Bool) (hyps : Array Expr) (tgt : Expr) :
    AtomM (Expr × Array (Source × Poly) × Poly) := do
  let fail {α} : AtomM α := throwError "polyrith failed: target is not an equality in semirings"
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).eq? | fail
  let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let sα ← synthInstanceQ (q(CommSemiring $α) : Q(Type v))
  let c ← mkCache sα
  let tgt := (← parse sα c e₁).sub (← parse sα c e₂)
  let rec
    processHyp src ty out := do
      if let some (β, e₁, e₂) := (← instantiateMVars ty).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
          return out.push (src, (← parse sα c e₁).sub (← parse sα c e₂))
      pure out
  let mut out := #[]
  if !only then
    for ldecl in ← getLCtx do
      out ← processHyp (.fvar ldecl.fvarId) ldecl.type out
  for hyp in hyps, i in [:hyps.size] do
    out ← processHyp (.input i) (← inferType hyp) out
  pure (α, out, tgt)
def createSageArgs (trace : Bool) (α : Expr) (atoms : Nat)
    (hyps : Array (Source × Poly)) (tgt : Poly) : Array String :=
  let hyps := hyps.map (toString ·.2) |>.toList.toString
  #[toString trace, toString α, toString atoms, hyps, toString tgt]
local instance : FromJson ℚ where fromJson?
  | .arr #[a, b] => return (← fromJson? a : ℤ) / (← fromJson? b : ℕ)
  | _ => .error "expected array with two elements"
def Poly.unNeg? : Poly → Option Poly
  | .mul a b => return .mul (← a.unNeg?) b
  | .const i => if i < 0 then some (.const (-i)) else none
  | .neg p => p
  | _ => none
def Poly.add' : Poly → Poly → Poly
  | .const 0, p => match p.unNeg? with
    | some np => .neg np
    | none => p
  | p, .const 0 => p
  | a, b => match b.unNeg? with
    | some nb => a.sub nb
    | none => a.add b
def Poly.mul' : Poly → Poly → Poly
  | .const 0, _ => .const 0
  | .const 1, p
  | p, .const 1 => p
  | a, b => a.mul b
def Poly.unDiv? : Poly → Option (Poly × ℕ)
  | .mul a b => do let (a, r) ← a.unDiv?; return (.mul' a b, r)
  | .const r => if r.num = 1 ∧ r.den ≠ 1 then some (.const r.num, r.den) else none
  | .neg p => do let (p, r) ← p.unDiv?; return (.neg p, r)
  | _ => none
def Poly.pow' : ℕ → ℕ → Poly
  | _, 0 => .const 1
  | i, 1 => .var i
  | i, k => .pow (.var i) (.const k)
def Poly.sumM {m : Type → Type*} {α : Type*} [Monad m] (a : Array α) (f : α → m Poly) : m Poly :=
  a.foldlM (init := .const 0) fun p a => return p.add' (← f a)
instance : FromJson Poly where
  fromJson? j := do
    Poly.sumM (← j.getArr?) fun j => do
      let mut mon := .const (← fromJson? (← j.getArrVal? 1))
      for j in ← (← j.getArrVal? 0).getArr? do
        mon := mon.mul' (.pow' (← fromJson? (← j.getArrVal? 0)) (← fromJson? (← j.getArrVal? 1)))
      pure mon
structure SageCoeffAndPower where
  coeffs : Array Poly
  power  : ℕ
  deriving FromJson, Repr
structure SageSuccess where
  trace : Option String := none
  data : Option SageCoeffAndPower := none
  deriving FromJson, Repr
structure SageError where
  name : String
  value : String
  deriving FromJson
def SageResult := Except SageError SageSuccess
instance : FromJson SageResult where fromJson? j := do
  if let .ok true := fromJson? <| j.getObjValD "success" then
    return .ok (← fromJson? j)
  else
    return .error (← fromJson? j)
def sageOutput (args : Array String) : IO SageResult := do
  let path := (← getMathlibDir) / "scripts" / "polyrith_sage.py"
  unless ← path.pathExists do
    throw <| IO.userError "could not find python script scripts/polyrith_sage.py"
  let out ← IO.Process.output { cmd := "python3", args := #[path.toString] ++ args }
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"scripts/polyrith_sage.py exited with code {out.exitCode}:\n\n{out.stderr}"
  match Json.parse out.stdout >>= fromJson? with
  | .ok v => return v
  | .error e => throw <| .userError e
def polyrith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (TSyntax `tactic)) := do
  IO.sleep 10 
  g.withContext <| AtomM.run .reducible do
    let (α, hyps', tgt) ← parseContext only hyps (← g.getType)
    let rec
      byRing msg := do
        let stx ← `(tactic| ring)
        try
          let ([], _) ← Elab.runTactic g stx | failure
          return .ok stx
        catch _ => throwError "{msg} and the goal is not provable by ring"
    if hyps'.isEmpty then
      return ← byRing "polyrith did not find any relevant hypotheses"
    let vars := (← get).atoms.size
    match ← sageOutput (createSageArgs traceOnly α vars hyps' tgt) with
    | .ok { trace, data } =>
      if let some trace := trace then logInfo trace
      if let some {coeffs := polys, power := pow} := data then
        let vars ← liftM <| (← get).atoms.mapM delab
        let p ← Poly.sumM (polys.zip hyps') fun (p, src, _) => do
          let h := .hyp (← delab (match src with | .input i => hyps[i]! | .fvar h => .fvar h))
          pure <| match p.unDiv? with
          | some (p, den) => (p.mul' h).div (.const den)
          | none => p.mul' h
        let stx := (withRef (← getRef) <| p.toSyntax vars).run
        let tac ←
          if let .const 0 := p then `(tactic| linear_combination)
          else if pow = 1 then `(tactic| linear_combination $stx:term)
          else `(tactic| linear_combination (exp := $(quote pow)) $stx:term)
        try
          guard (← Elab.runTactic g tac).1.isEmpty
        catch _ => throwError
          "polyrith found the following certificate, but it failed to close the goal:\n{stx}"
        pure <| .ok tac
      else if traceOnly then
        return .error g
      else throwError "internal error: no output available"
    | .error { name, value } =>
      throwError "polyrith failed to retrieve a solution from Sage! {name}: {value}"
syntax "polyrith" (&" only")? (" [" term,* "]")? : tactic
open Elab Tactic
elab_rules : tactic
  | `(tactic| polyrith%$tk $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.polyrith
    match ← polyrith (← getMainGoal) onlyTk.isSome hyps traceMe with
    | .ok stx =>
      replaceMainGoal []
      if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion tk stx
    | .error g => replaceMainGoal [g]
end Mathlib.Tactic.Polyrith