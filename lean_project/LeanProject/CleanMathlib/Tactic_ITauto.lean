import Batteries.Tactic.Exact
import Batteries.Tactic.Init
import Mathlib.Logic.Basic
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Util.AtomM
import Qq
namespace Mathlib.Tactic.ITauto
inductive AndKind | and | iff | eq
  deriving Lean.ToExpr, DecidableEq
instance : Inhabited AndKind := ⟨AndKind.and⟩
inductive IProp : Type
  | var : Nat → IProp            
  | true : IProp                 
  | false : IProp                
  | and' : AndKind → IProp → IProp → IProp 
  | or : IProp → IProp → IProp   
  | imp : IProp → IProp → IProp  
  deriving Lean.ToExpr, DecidableEq
@[match_pattern] def IProp.and : IProp → IProp → IProp := .and' .and
@[match_pattern] def IProp.iff : IProp → IProp → IProp := .and' .iff
@[match_pattern] def IProp.eq : IProp → IProp → IProp := .and' .eq
@[match_pattern] def IProp.not (a : IProp) : IProp := a.imp .false
@[match_pattern] def IProp.xor (a b : IProp) : IProp := (a.and b.not).or (b.and a.not)
instance : Inhabited IProp := ⟨IProp.true⟩
def AndKind.sides : AndKind → IProp → IProp → IProp × IProp
  | .and, A, B => (A, B)
  | _, A, B => (A.imp B, B.imp A)
def IProp.format : IProp → Std.Format
  | .var i => f!"v{i}"
  | .true => f!"⊤"
  | .false => f!"⊥"
  | .and p q => f!"({p.format} ∧ {q.format})"
  | .iff p q => f!"({p.format} ↔ {q.format})"
  | .eq p q => f!"({p.format} = {q.format})"
  | .or p q => f!"({p.format} ∨ {q.format})"
  | .imp p q => f!"({p.format} → {q.format})"
instance : Std.ToFormat IProp := ⟨IProp.format⟩
def AndKind.cmp (p q : AndKind) : Ordering := by
  cases p <;> cases q
  exacts [.eq, .lt, .lt, .gt, .eq, .lt, .gt, .gt, .eq]
def IProp.cmp (p q : IProp) : Ordering := by
  cases p <;> cases q
  case var.var p q => exact compare p q
  case true.true => exact .eq
  case false.false => exact .eq
  case and'.and' ap p₁ p₂ aq q₁ q₂ => exact (ap.cmp aq).then <| (p₁.cmp q₁).then (p₂.cmp q₂)
  case or.or p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  case imp.imp p₁ p₂ q₁ q₂ => exact (p₁.cmp q₁).then (p₂.cmp q₂)
  exacts [.lt, .lt, .lt, .lt, .lt,
          .gt, .lt, .lt, .lt, .lt,
          .gt, .gt, .lt, .lt, .lt,
          .gt, .gt, .gt, .lt, .lt,
          .gt, .gt, .gt, .gt, .lt,
          .gt, .gt, .gt, .gt, .gt]
instance : LT IProp := ⟨fun p q => p.cmp q = .lt⟩
instance : DecidableRel (@LT.lt IProp _) := fun _ _ => inferInstanceAs (Decidable (_ = _))
open Lean (Name)
inductive Proof
  | sorry : Proof
  | hyp (n : Name) : Proof
  | triv : Proof
  | exfalso' (p : Proof) : Proof
  | intro (x : Name) (p : Proof) : Proof
  | andLeft (ak : AndKind) (p : Proof) : Proof
  | andRight (ak : AndKind) (p : Proof) : Proof
  | andIntro (ak : AndKind) (p₁ p₂ : Proof) : Proof
  | curry (ak : AndKind) (p : Proof) : Proof
  | curry₂ (ak : AndKind) (p q : Proof) : Proof
  | app' : Proof → Proof → Proof
  | orImpL (p : Proof) : Proof
  | orImpR (p : Proof) : Proof
  | orInL (p : Proof) : Proof
  | orInR (p : Proof) : Proof
  | orElim' (p₁ : Proof) (x : Name) (p₂ p₃ : Proof) : Proof
  | decidableElim (classical : Bool) (p₁ x : Name) (p₂ p₃ : Proof) : Proof
  | em (classical : Bool) (p : Name) : Proof
  | impImpSimp (x : Name) (p : Proof) : Proof
  deriving Lean.ToExpr
instance : Inhabited Proof := ⟨Proof.triv⟩
def Proof.format : Proof → Std.Format
  | .sorry => "sorry"
  | .hyp i => Std.format i
  | .triv => "triv"
  | .exfalso' p => f!"(exfalso {p.format})"
  | .intro x p => f!"(fun {x} ↦ {p.format})"
  | .andLeft _ p => f!"{p.format} .1"
  | .andRight _ p => f!"{p.format} .2"
  | .andIntro _ p q => f!"⟨{p.format}, {q.format}⟩"
  | .curry _ p => f!"(curry {p.format})"
  | .curry₂ _ p q => f!"(curry {p.format} {q.format})"
  | .app' p q => f!"({p.format} {q.format})"
  | .orImpL p => f!"(orImpL {p.format})"
  | .orImpR p => f!"(orImpR {p.format})"
  | .orInL p => f!"(Or.inl {p.format})"
  | .orInR p => f!"(Or.inr {p.format})"
  | .orElim' p x q r => f!"({p.format}.elim (fun {x} ↦ {q.format}) (fun {x} ↦ {r.format})"
  | .em false p => f!"(Decidable.em {p})"
  | .em true p => f!"(Classical.em {p})"
  | .decidableElim _ p x q r => f!"({p}.elim (fun {x} ↦ {q.format}) (fun {x} ↦ {r.format})"
  | .impImpSimp _ p => f!"(impImpSimp {p.format})"
instance : Std.ToFormat Proof := ⟨Proof.format⟩
def Proof.exfalso : IProp → Proof → Proof
  | .false, p => p
  | _, p => .exfalso' p
def Proof.orElim : Proof → Name → Proof → Proof → Proof
  | .em cl p, x, q, r => .decidableElim cl p x q r
  | p, x, q, r => .orElim' p x q r
def Proof.app : Proof → Proof → Proof
  | .curry ak p, q => .curry₂ ak p q
  | .curry₂ ak p q, r => p.app (q.andIntro ak r)
  | .orImpL p, q => p.app q.orInL
  | .orImpR p, q => p.app q.orInR
  | .impImpSimp x p, q => p.app (.intro x q)
  | p, q => p.app' q
def Proof.check : Lean.NameMap IProp → Proof → Option IProp
  | _, .sorry A => some A
  | Γ, .hyp i => Γ.find? i
  | _, triv => some .true
  | Γ, .exfalso' A p => guard (p.check Γ = some .false) *> pure A
  | Γ, .intro x A p => do let B ← p.check (Γ.insert x A); pure (.imp A B)
  | Γ, .andLeft ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).1
  | Γ, .andRight ak p => do
    let .and' ak' A B ← p.check Γ | none
    guard (ak = ak') *> pure (ak.sides A B).2
  | Γ, .andIntro .and p q => do
    let A ← p.check Γ; let B ← q.check Γ
    pure (A.and B)
  | Γ, .andIntro ak p q => do
    let .imp A B ← p.check Γ | none
    let C ← q.check Γ; guard (C = .imp B A) *> pure (A.and' ak B)
  | Γ, .curry ak p => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let (A', B') := ak.sides A B
    guard (ak = ak') *> pure (A'.imp $ B'.imp C)
  | Γ, .curry₂ ak p q => do
    let .imp (.and' ak' A B) C ← p.check Γ | none
    let A₂ ← q.check Γ
    let (A', B') := ak.sides A B
    guard (ak = ak' ∧ A₂ = A') *> pure (B'.imp C)
  | Γ, .app' p q => do
    let .imp A B ← p.check Γ | none
    let A' ← q.check Γ
    guard (A = A') *> pure B
  | Γ, .orImpL B p => do
    let .imp (.or A B') C ← p.check Γ | none
    guard (B = B') *> pure (A.imp C)
  | Γ, .orImpR A p => do
    let .imp (.or A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
  | Γ, .orInL B p => do let A ← p.check Γ; pure (A.or B)
  | Γ, .orInR A p => do let B ← p.check Γ; pure (A.or B)
  | Γ, .orElim' p x q r => do
    let .or A B ← p.check Γ | none
    let C ← q.check (Γ.insert x A)
    let C' ← r.check (Γ.insert x B)
    guard (C = C') *> pure C
  | _, .em _ _ A => pure (A.or A.not)
  | Γ, .decidableElim _ A _ x p₂ p₃ => do
    let C ← p₂.check (Γ.insert x A)
    let C' ← p₃.check (Γ.insert x A.not)
    guard (C = C') *> pure C
  | Γ, .impImpSimp _ A p => do
    let .imp (.imp A' B) C ← p.check Γ | none
    guard (A = A') *> pure (B.imp C)
-/
@[inline] def freshName : StateM Nat Name := fun n => (Name.mkSimple s!"h{n}", n + 1)
def Context := Lean.RBMap IProp Proof IProp.cmp
def Context.format (Γ : Context) : Std.Format :=
  Γ.fold (init := "") fun f P p => P.format ++ " := " ++ p.format ++ ",\n" ++ f
instance : Std.ToFormat Context := ⟨Context.format⟩
partial def Context.add : IProp → Proof → Context → Except (IProp → Proof) Context
  | .true, _, Γ => pure Γ
  | .false, p, _ => throw fun A => .exfalso A p
  | .and' ak A B, p, Γ => do
    let (A, B) := ak.sides A B
    let Γ ← Γ.add A (p.andLeft ak)
    Γ.add B (p.andRight ak)
  | .imp .false _, _, Γ => pure Γ
  | .imp .true A, p, Γ => Γ.add A (p.app .triv)
  | .imp (.and' ak A B) C, p, Γ =>
    let (A, B) := ak.sides A B
    Γ.add (A.imp (B.imp C)) (p.curry ak)
  | .imp (.or A B) C, p, Γ => do
    let Γ ← Γ.add (A.imp C) p.orImpL
    Γ.add (B.imp C) p.orImpR
  | .imp _ .true, _, Γ => pure Γ
  | A, p, Γ => pure (Γ.insert A p)
@[inline] def Context.withAdd (Γ : Context) (A : IProp) (p : Proof) (B : IProp)
    (f : Context → IProp → StateM Nat (Bool × Proof)) : StateM Nat (Bool × Proof) :=
  match Γ.add A p with
  | .ok Γ_A => f Γ_A B
  | .error p => pure (true, p B)
def mapProof (f : Proof → Proof) : Bool × Proof → Bool × Proof
  | (b, p) => (b, f p)
def isOk : (Bool × Proof) × Nat → Option (Proof × Nat)
  | ((false, _), _) => none
  | ((true, p), n) => some (p, n)
def whenOk : Bool → IProp → StateM Nat (Bool × Proof) → StateM Nat (Bool × Proof)
  | false, _, _ => pure (false, .sorry)
  | true, _, f => f
mutual
partial def search (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) := do
  if let some p := Γ.find? B then return (true, p)
  fun n =>
  let search₁ := Γ.fold (init := none) fun r A p => do
    if let some r := r then return r
    let .imp A' C := A | none
    if let some q := Γ.find? A' then
      isOk <| Context.withAdd (Γ.erase A) C (p.app q) B prove n
    else
      let .imp A₁ A₂ := A' | none
      let Γ : Context := Γ.erase A
      let (a, n) := freshName n
      let (p₁, n) ← isOk <| Γ.withAdd A₁ (.hyp a) A₂ (fun Γ_A₁ A₂ =>
        Γ_A₁.withAdd (IProp.imp A₂ C) (.impImpSimp a p) A₂ prove) n
      isOk <| Γ.withAdd C (p.app (.intro a p₁)) B prove n
  if let some (r, n) := search₁ then
    ((true, r), n)
  else if let .or B₁ B₂ := B then
    match (mapProof .orInL <$> prove Γ B₁) n with
    | ((false, _), _) => (mapProof .orInR <$> prove Γ B₂) n
    | r => r
  else ((false, .sorry), n)
partial def prove (Γ : Context) (B : IProp) : StateM Nat (Bool × Proof) :=
  match B with
  | .true => pure (true, .triv)
  | .imp A B => do
    let a ← freshName
    mapProof (.intro a) <$> Γ.withAdd A (.hyp a) B prove
  | .and' ak A B => do
    let (A, B) := ak.sides A B
    let (ok, p) ← prove Γ A
    mapProof (p.andIntro ak) <$> whenOk ok B (prove Γ B)
  | B =>
    Γ.fold
      (init := fun found Γ => bif found then prove Γ B else search Γ B)
      (f := fun IH A p found Γ => do
        if let .or A₁ A₂ := A then
          let Γ : Context := Γ.erase A
          let a ← freshName
          let (ok, p₁) ← Γ.withAdd A₁ (.hyp a) B fun Γ _ => IH true Γ
          mapProof (.orElim p a p₁) <$>
            whenOk ok B (Γ.withAdd A₂ (.hyp a) B fun Γ _ => IH true Γ)
        else IH found Γ)
      (found := false) (Γ := Γ)
end
open Lean Qq Meta
partial def reify (e : Q(Prop)) : AtomM IProp :=
  match e with
  | ~q(True) => return .true
  | ~q(False) => return .false
  | ~q(¬ $a) => return .not (← reify a)
  | ~q($a ∧ $b) => return .and (← reify a) (← reify b)
  | ~q($a ∨ $b) => return .or (← reify a) (← reify b)
  | ~q($a ↔ $b) => return .iff (← reify a) (← reify b)
  | ~q(Xor' $a $b) => return .xor (← reify a) (← reify b)
  | ~q(@Eq Prop $a $b) => return .eq (← reify a) (← reify b)
  | ~q(@Ne Prop $a $b) => return .not (.eq (← reify a) (← reify b))
  | e =>
    if e.isArrow then return .imp (← reify e.bindingDomain!) (← reify e.bindingBody!)
    else return .var (← AtomM.addAtom e).1
partial def applyProof (g : MVarId) (Γ : NameMap Expr) (p : Proof) : MetaM Unit :=
  match p with
  | .sorry => throwError "itauto failed\n{g}"
  | .hyp n => do g.assignIfDefeq (← liftOption (Γ.find? n))
  | .triv => g.assignIfDefeq q(trivial)
  | .exfalso' p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q(False)
    g.assignIfDefeq q(@False.elim $A $t)
    applyProof t.mvarId! Γ p
  | .intro x p => do
    let (e, g) ← g.intro x; g.withContext do
      applyProof g (Γ.insert x (.fvar e)) p
  | .andLeft .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefeq q(And.left $t)
    applyProof t.mvarId! Γ p
  | .andLeft .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefeq q(Iff.mp $t)
    applyProof t.mvarId! Γ p
  | .andLeft .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefeq q(cast $t)
    applyProof t.mvarId! Γ p
  | .andRight .and p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ∧ $B)
    g.assignIfDefeq q(And.right $t)
    applyProof t.mvarId! Γ p
  | .andRight .iff p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A ↔ $B)
    g.assignIfDefeq q(Iff.mpr $t)
    applyProof t.mvarId! Γ p
  | .andRight .eq p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ q($A = $B)
    g.assignIfDefeq q(cast (Eq.symm $t))
    applyProof t.mvarId! Γ p
  | .andIntro .and p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ (u := .zero) A
    let t₂ ← mkFreshExprMVarQ (u := .zero) B
    g.assignIfDefeq q(And.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .iff p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefeq q(Iff.intro $t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .andIntro .eq p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q($B → $A)
    g.assignIfDefeq q(propext (Iff.intro $t₁ $t₂))
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .app' p q => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ (u := .zero) A
    g.assignIfDefeq q($t₁ $t₂)
    applyProof t₁.mvarId! Γ p
    applyProof t₂.mvarId! Γ q
  | .orInL p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ (u := .zero) A
    g.assignIfDefeq q(@Or.inl $A $B $t)
    applyProof t.mvarId! Γ p
  | .orInR p => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let t ← mkFreshExprMVarQ (u := .zero) B
    g.assignIfDefeq q(@Or.inr $A $B $t)
    applyProof t.mvarId! Γ p
  | .orElim' p x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let B ← mkFreshExprMVarQ q(Prop)
    let C ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A ∨ $B)
    let t₂ ← mkFreshExprMVarQ q($A → $C)
    let t₃ ← mkFreshExprMVarQ q($B → $C)
    g.assignIfDefeq q(Or.elim $t₁ $t₂ $t₃)
    applyProof t₁.mvarId! Γ p
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₁
    let (e, t₃) ← t₃.mvarId!.intro x; t₃.withContext do
      applyProof t₃ (Γ.insert x (.fvar e)) p₂
  | .em false n => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    g.assignIfDefeq q(@Decidable.em $A $e)
  | .em true n => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    g.assignIfDefeq q(@Classical.em $A)
  | .decidableElim false n x p₁ p₂ => do
    let A ← mkFreshExprMVarQ q(Prop)
    let e : Q(Decidable $A) ← liftOption (Γ.find? n)
    let .true ← Meta.isDefEq (← Meta.inferType e) q(Decidable $A) | failure
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefeq q(@dite $B $A $e $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .decidableElim true n x p₁ p₂ => do
    let A : Q(Prop) ← liftOption (Γ.find? n)
    let B ← mkFreshExprMVarQ q(Prop)
    let t₁ ← mkFreshExprMVarQ q($A → $B)
    let t₂ ← mkFreshExprMVarQ q(¬$A → $B)
    g.assignIfDefeq q(@Classical.byCases $A $B $t₁ $t₂)
    let (e, t₁) ← t₁.mvarId!.intro x; t₁.withContext do
      applyProof t₁ (Γ.insert x (.fvar e)) p₁
    let (e, t₂) ← t₂.mvarId!.intro x; t₂.withContext do
      applyProof t₂ (Γ.insert x (.fvar e)) p₂
  | .curry .. | .curry₂ .. | .orImpL .. | .orImpR .. | .impImpSimp .. => do
    let (e, g) ← g.intro1; g.withContext do
      applyProof g (Γ.insert e.name (.fvar e)) (p.app (.hyp e.name))
def itautoCore (g : MVarId)
    (useDec useClassical : Bool) (extraDec : Array Expr) : MetaM Unit := do
  AtomM.run (← getTransparency) do
    let mut hs := mkRBMap ..
    let t ← g.getType
    let (g, t) ← if ← isProp t then pure (g, ← reify t) else pure (← g.exfalso, .false)
    let mut Γ : Except (IProp → Proof) ITauto.Context := .ok (mkRBMap ..)
    let mut decs := mkRBMap ..
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        let e := ldecl.type
        if ← isProp e then
          let A ← reify e
          let n := ldecl.fvarId.name
          hs := hs.insert n (Expr.fvar ldecl.fvarId)
          Γ := do (← Γ).add A (.hyp n)
        else
          if let .const ``Decidable _ := e.getAppFn then
            let p : Q(Prop) := e.appArg!
            if useDec then
              let A ← reify p
              decs := decs.insert A (false, Expr.fvar ldecl.fvarId)
    let addDec (force : Bool) (decs : RBMap IProp (Bool × Expr) IProp.cmp) (e : Q(Prop)) := do
      let A ← reify e
      let dec_e := q(Decidable $e)
      let res ← trySynthInstance q(Decidable $e)
      if !(res matches .some _) && !useClassical then
        if force then _ ← synthInstance dec_e
        pure decs
      else
        pure (decs.insert A (match res with | .some e => (false, e) | _ => (true, e)))
    decs ← extraDec.foldlM (addDec true) decs
    if useDec then
      let mut decided := mkRBTree Nat compare
      if let .ok Γ' := Γ then
        decided := Γ'.fold (init := decided) fun m p _ =>
          match p with
          | .var i => m.insert i
          | .not (.var i) => m.insert i
          | _ => m
      let ats := (← get).atoms
      for e in ats, i in [0:ats.size] do
        if !decided.contains i then
          decs ← addDec false decs e
    for (A, cl, pf) in decs do
      let n ← mkFreshId
      hs := hs.insert n pf
      Γ := return (← Γ).insert (A.or A.not) (.em cl n)
    let p : Proof :=
      match Γ with
      | .ok Γ => (prove Γ t 0).1.2
      | .error p => p t
    applyProof g hs p
open Elab Tactic
syntax (name := itauto) "itauto" "!"? (" *" <|> (" [" term,* "]"))? : tactic
elab_rules : tactic
  | `(tactic| itauto $[!%$cl]?) => liftMetaTactic (itautoCore · false cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? *) => liftMetaTactic (itautoCore · true cl.isSome #[] *> pure [])
  | `(tactic| itauto $[!%$cl]? [$hs,*]) => withMainContext do
    let hs ← hs.getElems.mapM (Term.elabTermAndSynthesize · none)
    liftMetaTactic (itautoCore · true cl.isSome hs *> pure [])
@[inherit_doc itauto] syntax (name := itauto!) "itauto!" (" *" <|> (" [" term,* "]"))? : tactic
macro_rules
  | `(tactic| itauto!) => `(tactic| itauto !)
  | `(tactic| itauto! *) => `(tactic| itauto ! *)
  | `(tactic| itauto! [$hs,*]) => `(tactic| itauto ! [$hs,*])
end Mathlib.Tactic.ITauto