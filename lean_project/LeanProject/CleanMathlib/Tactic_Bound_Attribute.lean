import Mathlib.Algebra.Group.ZeroOne
import Mathlib.Tactic.Bound.Init
import Qq
import Aesop
open Lean (MetaM)
open Qq
namespace Mathlib.Tactic.Bound
initialize Lean.registerTraceClass `bound.attribute
variable {u : Lean.Level} {α : Q(Type u)}
def isZero (e : Q($α)) : MetaM Bool :=
  match e with
  | ~q(@OfNat.ofNat.{u} _ (nat_lit 0) $i) => return true
  | _ => return false
def ineqPriority (a b : Q($α)) : MetaM ℕ := do
  return if (← isZero a) || (← isZero b) then 1 else 10
partial def hypPriority (hyp : Q(Prop)) : MetaM ℕ := do
  match hyp with
    | ~q($a ∧ $b) => pure <| (← hypPriority a) + (← hypPriority b)
    | ~q($a ∨ $b) => pure <| 100 + (← hypPriority a) + (← hypPriority b)
    | ~q(@LE.le _ $i $a $b) => ineqPriority a b
    | ~q(@LT.lt _ $i $a $b) => ineqPriority a b
    | ~q(@GE.ge _ $i $b $a) => ineqPriority a b
    | ~q(@GT.gt _ $i $b $a) => ineqPriority a b
    | _ => pure 0
def typePriority (decl : Lean.Name) (type : Lean.Expr) : MetaM ℕ :=
  Lean.Meta.forallTelescope type fun xs t ↦ do
    checkResult t
    xs.foldlM (fun (t : ℕ) x ↦ do return t + (← argPriority x)) 0
  where
  argPriority (x : Lean.Expr) : MetaM ℕ := do
    hypPriority (← Lean.Meta.inferType x)
  checkResult (t : Q(Prop)) : MetaM Unit := do match t with
    | ~q(@LE.le _ $i $a $b) => return ()
    | ~q(@LT.lt _ $i $a $b) => return ()
    | ~q(@GE.ge _ $i $b $a) => return ()
    | ~q(@GT.gt _ $i $b $a) => return ()
    | _ => throwError (f!"`{decl}` has invalid type `{type}` as a 'bound' lemma: \
                          it should be an inequality")
def declPriority (decl : Lean.Name) : Lean.MetaM ℕ := do
  match (← Lean.getEnv).find? decl with
    | some info => do
        typePriority decl info.type
    | none => throwError "unknown declaration {decl}"
def scoreToConfig (decl : Lean.Name) (score : ℕ) : Aesop.Frontend.RuleConfig :=
  let (phase, priority) := match score with
    | 0 => (Aesop.PhaseName.norm, 0)  
    | s => (Aesop.PhaseName.safe, s)
  { term? := some (Lean.mkIdent decl)
    phase? := phase
    priority? := some (Aesop.Frontend.Priority.int priority)
    builder? := some (.regular .apply)
    builderOptions := {}
    ruleSets := ⟨#[`Bound]⟩ }
initialize Lean.registerBuiltinAttribute {
  name := `bound
  descr := "Register a theorem as an apply rule for the `bound` tactic."
  applicationTime := .afterCompilation
  add := fun decl stx attrKind => Lean.withRef stx do
    let score ← Aesop.runTermElabMAsCoreM <| declPriority decl
    trace[bound.attribute] "'{decl}' has score '{score}'"
    let context ← Aesop.runMetaMAsCoreM Aesop.ElabM.Context.forAdditionalGlobalRules
    let (rule, ruleSets) ← Aesop.runTermElabMAsCoreM <|
      (scoreToConfig decl score).buildGlobalRule.run context
    for ruleSet in ruleSets do
      Aesop.Frontend.addGlobalRule ruleSet rule attrKind (checkNotExists := true)
  erase := fun decl =>
    let ruleFilter := { name := decl, scope := .global, builders := #[], phases := #[] }
    Aesop.Frontend.eraseGlobalRules Aesop.RuleSetNameFilter.all ruleFilter (checkExists := true)
}
macro "bound_forward" : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Bound):ident]))
end Mathlib.Tactic.Bound