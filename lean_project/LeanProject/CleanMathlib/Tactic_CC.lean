import Mathlib.Tactic.CC.Addition
universe u
open Lean Meta Elab Tactic Std
namespace Mathlib.Tactic.CC
namespace CCState
open CCM
def mkCore (config : CCConfig) : CCState :=
  let s : CCState := { config with }
  s.mkEntryCore (.const ``True []) true false |>.mkEntryCore (.const ``False []) true false
def mkUsingHsCore (config : CCConfig) : MetaM CCState := do
  let ctx ← getLCtx
  let ctx ← instantiateLCtxMVars ctx
  let (_, c) ← CCM.run (ctx.forM fun dcl => do
    unless dcl.isImplementationDetail do
      if ← isProp dcl.type then
        add dcl.type dcl.toExpr) { mkCore config with }
  return c.toCCState
def rootsCore (ccs : CCState) (nonsingleton : Bool) : List Expr :=
  ccs.getRoots #[] nonsingleton |>.toList
def incGMT (ccs : CCState) : CCState :=
  { ccs with gmt := ccs.gmt + 1 }
def internalize (ccs : CCState) (e : Expr) : MetaM CCState := do
  let (_, c) ← CCM.run (CCM.internalize e) { ccs with }
  return c.toCCState
def add (ccs : CCState) (H : Expr) : MetaM CCState := do
  let type ← inferType H
  unless ← isProp type do
    throwError "CCState.add failed, given expression is not a proof term"
  let (_, c) ← CCM.run (CCM.add type H) { ccs with }
  return c.toCCState
def isEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isEqv e₁ e₂) { ccs with }
  return b
def isNotEqv (ccs : CCState) (e₁ e₂ : Expr) : MetaM Bool := do
  let (b, _) ← CCM.run (CCM.isNotEqv e₁ e₂) { ccs with }
  return b
def eqvProof (ccs : CCState) (e₁ e₂ : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e₁ e₂) { ccs with }
    | throwError "CCState.eqvProof failed to build proof"
  return r
def proofFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``True [])) { ccs with }
    | throwError "CCState.proofFor failed to build proof"
  mkAppM ``of_eq_true #[r]
def refutationFor (ccs : CCState) (e : Expr) : MetaM Expr := do
  let (some r, _) ← CCM.run (CCM.getEqProof e (.const ``False [])) { ccs with }
    | throwError "CCState.refutationFor failed to build proof"
  mkAppM ``of_eq_false #[r]
def proofForFalse (ccs : CCState) : MetaM Expr := do
  let (some pr, _) ← CCM.run CCM.getInconsistencyProof { ccs with }
    | throwError "CCState.proofForFalse failed, state is not inconsistent"
  return pr
def mkUsingHs : MetaM CCState :=
  CCState.mkUsingHsCore {}
def roots (s : CCState) : List Expr :=
  CCState.rootsCore s true
instance : ToMessageData CCState :=
  ⟨fun s => CCState.ppEqcs s true⟩
partial def eqcOfCore (s : CCState) (e : Expr) (f : Expr) (r : List Expr) : List Expr :=
  let n := s.next e
  if n == f then e :: r else eqcOfCore s n f (e :: r)
def eqcOf (s : CCState) (e : Expr) : List Expr :=
  s.eqcOfCore e e []
def eqcSize (s : CCState) (e : Expr) : Nat :=
  s.eqcOf e |>.length
partial def foldEqcCore {α} (s : CCState) (f : α → Expr → α) (first : Expr) (c : Expr) (a : α) :
    α :=
  let new_a := f a c
  let next := s.next c
  if next == first then new_a else foldEqcCore s f first next new_a
def foldEqc {α} (s : CCState) (e : Expr) (a : α) (f : α → Expr → α) : α :=
  foldEqcCore s f e e a
def foldEqcM {α} {m : Type → Type} [Monad m] (s : CCState) (e : Expr) (a : α)
    (f : α → Expr → m α) : m α :=
  foldEqc s e (return a) fun act e => do
    let a ← act
    f a e
end CCState
def _root_.Lean.MVarId.cc (m : MVarId) (cfg : CCConfig := {}) : MetaM Unit := do
  let (_, m) ← m.intros
  m.withContext do
    let s ← CCState.mkUsingHsCore cfg
    let t ← m.getType >>= instantiateMVars
    let s ← s.internalize t
    if s.inconsistent then
        let pr ← s.proofForFalse
        mkAppOptM ``False.elim #[t, pr] >>= m.assign
    else
      let tr := Expr.const ``True []
      let b ← s.isEqv t tr
      if b then
        let pr ← s.eqvProof t tr
        mkAppM ``of_eq_true #[pr] >>= m.assign
      else
        let dbg ← getBoolOption `trace.Meta.Tactic.cc.failure false
        if dbg then
          throwError m!"cc tactic failed, equivalence classes: {s}"
        else
          throwError "cc tactic failed"
declare_config_elab elabCCConfig CCConfig
open Parser.Tactic in
elab (name := _root_.Mathlib.Tactic.cc) "cc" cfg:optConfig : tactic => do
  let cfg ← elabCCConfig cfg
  withMainContext <| liftMetaFinishingTactic (·.cc cfg)
end Mathlib.Tactic.CC