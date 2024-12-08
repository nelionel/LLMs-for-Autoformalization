import Mathlib.Algebra.Group.Nat.Basic
import Mathlib.Tactic.ByContra
open Lean hiding Literal HashMap
open Std (HashMap)
namespace Sat
inductive Literal
  | pos : Nat → Literal
  | neg : Nat → Literal
def Literal.ofInt (i : Int) : Literal :=
  if i < 0 then Literal.neg (-i-1).toNat else Literal.pos (i-1).toNat
def Literal.negate : Literal → Literal
  | pos i => neg i
  | neg i => pos i
instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr
  | Literal.pos i => mkApp (mkConst ``Literal.pos) (mkRawNatLit i)
  | Literal.neg i => mkApp (mkConst ``Literal.neg) (mkRawNatLit i)
def Clause := List Literal
def Clause.nil : Clause := []
def Clause.cons : Literal → Clause → Clause := List.cons
abbrev Fmla := List Clause
def Fmla.one (c : Clause) : Fmla := [c]
def Fmla.and (a b : Fmla) : Fmla := a ++ b
structure Fmla.subsumes (f f' : Fmla) : Prop where
  prop : ∀ x, x ∈ f' → x ∈ f
theorem Fmla.subsumes_self (f : Fmla) : f.subsumes f := ⟨fun _ h ↦ h⟩
theorem Fmla.subsumes_left (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₁ :=
  ⟨fun _ h ↦ H.1 _ <| List.mem_append.2 <| Or.inl h⟩
theorem Fmla.subsumes_right (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₂ :=
  ⟨fun _ h ↦ H.1 _ <| List.mem_append.2 <| Or.inr h⟩
def Valuation := Nat → Prop
def Valuation.neg (v : Valuation) : Literal → Prop
  | Literal.pos i => ¬ v i
  | Literal.neg i => v i
def Valuation.satisfies (v : Valuation) : Clause → Prop
  | [] => False
  | l::c => v.neg l → v.satisfies c
structure Valuation.satisfies_fmla (v : Valuation) (f : Fmla) : Prop where
  prop : ∀ c, c ∈ f → v.satisfies c
def Fmla.proof (f : Fmla) (c : Clause) : Prop :=
  ∀ v : Valuation, v.satisfies_fmla f → v.satisfies c
theorem Fmla.proof_of_subsumes {f : Fmla} {c : Clause}
    (H : Fmla.subsumes f (Fmla.one c)) : f.proof c :=
  fun _ h ↦ h.1 _ <| H.1 _ <| List.Mem.head ..
theorem Valuation.by_cases {v : Valuation} {l}
    (h₁ : v.neg l.negate → False) (h₂ : v.neg l → False) : False :=
match l with
| Literal.pos _ => h₂ h₁
| Literal.neg _ => h₁ h₂
def Valuation.implies (v : Valuation) (p : Prop) : List Prop → Nat → Prop
  | [], _ => p
  | a::as, n => (v n ↔ a) → v.implies p as (n+1)
def Valuation.mk : List Prop → Valuation
  | [], _ => False
  | a::_, 0 => a
  | _::as, n+1 => mk as n
theorem Valuation.mk_implies {p} {as ps} (as₁) : as = List.reverseAux as₁ ps →
    (Valuation.mk as).implies p ps as₁.length → p := by
  induction ps generalizing as₁ with
  | nil => exact fun _ ↦ id
  | cons a as ih =>
    refine fun e H ↦ @ih (a::as₁) e (H ?_)
    subst e; clear ih H
    suffices ∀ n n', n' = List.length as₁ + n →
      ∀ bs, mk (as₁.reverseAux bs) n' ↔ mk bs n from this 0 _ rfl (a::as)
    induction as₁ with
    | nil => simp
    | cons b as₁ ih => simpa using fun n bs ↦ ih (n+1) _ (Nat.succ_add ..) _
structure Fmla.reify (v : Valuation) (f : Fmla) (p : Prop) : Prop where
  prop : ¬ v.satisfies_fmla f → p
variable {v : Valuation}
theorem Fmla.refute {p : Prop} {ps} (f : Fmla) (hf : f.proof [])
    (hv : ∀ v, Valuation.implies v (Fmla.reify v f p) ps 0) : p :=
  (Valuation.mk_implies [] rfl (hv _)).1 (hf _)
theorem Fmla.reify_or {f₁ : Fmla} {a : Prop} {f₂ : Fmla} {b : Prop}
    (h₁ : Fmla.reify v f₁ a) (h₂ : Fmla.reify v f₂ b) : Fmla.reify v (f₁.and f₂) (a ∨ b) := by
  refine ⟨fun H ↦ by_contra fun hn ↦ H ⟨fun c h ↦ by_contra fun hn' ↦ ?_⟩⟩
  rcases List.mem_append.1 h with h | h
  · exact hn <| Or.inl <| h₁.1 fun Hc ↦ hn' <| Hc.1 _ h
  · exact hn <| Or.inr <| h₂.1 fun Hc ↦ hn' <| Hc.1 _ h
structure Clause.reify (v : Valuation) (c : Clause) (p : Prop) : Prop where
  prop : ¬ v.satisfies c → p
theorem Fmla.reify_one {c : Clause} {a : Prop} (h : Clause.reify v c a) :
    Fmla.reify v (Fmla.one c) a :=
  ⟨fun H ↦ h.1 fun h ↦ H ⟨fun | _, List.Mem.head .. => h⟩⟩
structure Literal.reify (v : Valuation) (l : Literal) (p : Prop) : Prop where
  prop : v.neg l → p
theorem Clause.reify_and {l : Literal} {a : Prop} {c : Clause} {b : Prop}
    (h₁ : Literal.reify v l a) (h₂ : Clause.reify v c b) :
    Clause.reify v (Clause.cons l c) (a ∧ b) :=
  ⟨fun H ↦ ⟨h₁.1 (by_contra fun hn ↦ H hn.elim), h₂.1 fun h ↦ H fun _ ↦ h⟩⟩
theorem Clause.reify_zero : Clause.reify v Clause.nil True := ⟨fun _ ↦ trivial⟩
theorem Clause.reify_one {l : Literal} {a : Prop}
    (h₁ : Literal.reify v l a) : Clause.reify v (Clause.nil.cons l) a :=
  ⟨fun H ↦ ((Clause.reify_and h₁ Clause.reify_zero).1 H).1⟩
theorem Literal.reify_pos {a : Prop} {n : ℕ} (h : v n ↔ a) : (Literal.pos n).reify v ¬a := ⟨mt h.2⟩
theorem Literal.reify_neg {a : Prop} {n : ℕ} (h : v n ↔ a) : (Literal.neg n).reify v a := ⟨h.1⟩
end Sat
namespace Mathlib.Tactic.Sat
structure Clause where
  lits : Array Int
  expr : Expr
  proof : Expr
def buildClause (arr : Array Int) : Expr :=
  let nil  := mkConst ``Sat.Clause.nil
  let cons := mkConst ``Sat.Clause.cons
  arr.foldr (fun i e ↦ mkApp2 cons (toExpr <| Sat.Literal.ofInt i) e) nil
partial def buildConj (arr : Array (Array Int)) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 => mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!)
  | len =>
    let mid := start + len / 2
    mkApp2 (mkConst ``Sat.Fmla.and) (buildConj arr start mid) (buildConj arr mid stop)
partial def buildClauses (arr : Array (Array Int)) (ctx : Expr) (start stop : Nat)
  (f p : Expr) (accum : Nat × HashMap Nat Clause) : Nat × HashMap Nat Clause :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 =>
    let c := f.appArg!
    let proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    let n := accum.1 + 1
    (n, accum.2.insert n { lits := arr[start]!, expr := c, proof })
  | len =>
    let mid := start + len / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
    let accum := buildClauses arr ctx start mid f₁ p₁ accum
    buildClauses arr ctx mid stop f₂ p₂ accum
structure LClause where
  lits : Array Int
  expr : Expr
  depth : Nat
partial def buildProofStep (db : HashMap Nat Clause)
  (ns pf : Array Int) (ctx clause : Expr) : Except String Expr := Id.run do
  let mut lams := #[]
  let mut args := #[]
  let mut gctx : HashMap Nat LClause := {}
  for i in pf do
    let i := i.natAbs
    let some cl := db[i]? | return Except.error "missing clause"
    if !gctx.contains i then
      lams := lams.push (mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr)
      args := args.push cl.proof
      gctx := gctx.insert i {
        lits := cl.lits
        expr := cl.expr
        depth := args.size
      }
  let n := args.size
  let mut f :=
    (mkAppN · args) ∘
    lams.foldr (mkLambda `c default) ∘
    mkLambda `v default (mkConst ``Sat.Valuation) ∘
    mkLambda `hv default (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) (mkBVar 0) ctx)
  let v depth := mkBVar (depth + 1)
  let hv depth := mkBVar depth
  lams := #[]
  let mut clause := clause
  let mut depth := 0
  let mut lctx : HashMap Int Nat := {}
  for i in ns do
    let l := clause.appFn!.appArg!
    clause := clause.appArg!
    lams := lams.push (mkApp2 (mkConst ``Sat.Valuation.neg) (v depth) l)
    depth := depth.succ
    lctx := lctx.insert i depth
  f := f ∘ lams.foldr (mkLambda `h default)
  for (step : Int) in pf do
    if step < 0 then return Except.error "unimplemented: RAT step"
    let some cl := gctx[step.toNat]? | return Except.error "missing clause"
    let mut unit := none
    for i in cl.lits do
      unless lctx.contains i do
        if unit.isSome then return Except.error s!"not unit: {cl.lits}"
        depth := depth.succ
        unit := some i
    let mut pr := mkApp2 (mkBVar (depth + n + 2 - cl.depth)) (v depth) (hv depth)
    for i in cl.lits do
      pr := mkApp pr <| mkBVar (match lctx[i]? with | some k => depth - k | _ => 0)
    let some u := unit | return Except.ok <| f pr
    let lit := toExpr <| Sat.Literal.ofInt u
    let nlit := toExpr <| Sat.Literal.ofInt (-u)
    let d1 := depth-1
    let app := mkApp3 (mkConst ``Sat.Valuation.by_cases) (v d1) nlit <|
      mkLambda `h default (mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) lit) pr
    let dom := mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) nlit
    f := fun e ↦ f <| mkApp app <| mkLambda `h default dom e
    lctx := lctx.insert (-u) depth
  return Except.error s!"no refutation: {ns}, {pf}, {lctx.toList}"
inductive LRATStep
  | 
    add (id : Nat) (lits : Array Int) (proof : Array Int) : LRATStep
  | 
    del (ids : Array Nat) : LRATStep
partial def buildProof (arr : Array (Array Int)) (ctx ctx' : Expr)
  (steps : Array LRATStep) : MetaM Expr := do
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      match buildProofStep db ns pf ctx e with
      | Except.ok proof =>
        if ns.isEmpty then return proof
        db := db.insert i { lits := ns, expr := e, proof }
      | Except.error msg => throwError msg
  throwError "failed to prove empty clause"
partial def buildReify (ctx ctx' proof : Expr) (nvars : Nat) : Expr × Expr := Id.run do
  let (e, pr) := reifyFmla ctx'
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars-i-1
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h default ty pr
  pr := mkLambda `v default (mkConst ``Sat.Valuation) pr
  let mut e := e.lowerLooseBVars (nvars+1) (nvars+1)
  let cons := mkApp (mkConst ``List.cons [levelZero]) (mkSort levelZero)
  let nil := mkApp (mkConst ``List.nil [levelZero]) (mkSort levelZero)
  let rec mkPS depth e
  | 0 => e
  | n+1 => mkPS (depth+1) (mkApp2 cons (mkBVar depth) e) n
  pr := mkApp5 (mkConst ``Sat.Fmla.refute) e (mkPS 0 nil nvars) ctx proof pr
  for _ in [0:nvars] do
    e := mkForall `a default (mkSort levelZero) e
    pr := mkLambda `a default (mkSort levelZero) pr
  pure (e, pr)
where
  v := mkBVar nvars
  reifyFmla f :=
    match f.getAppFn.constName! with
    | ``Sat.Fmla.and =>
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      let (e₁, h₁) := reifyFmla f₁
      let (e₂, h₂) := reifyFmla f₂
      (mkApp2 (mkConst ``Or) e₁ e₂, mkApp7 (mkConst ``Sat.Fmla.reify_or) v f₁ e₁ f₂ e₂ h₁ h₂)
    | ``Sat.Fmla.one =>
      let c := f.appArg!
      let (e, h) := reifyClause c
      (e, mkApp4 (mkConst ``Sat.Fmla.reify_one) v c e h)
    | _ => panic! "not a valid formula"
  reifyClause c :=
    if c.appFn!.isConst then
      (mkConst ``True, mkApp (mkConst ``Sat.Clause.reify_zero) v)
    else reifyClause1 c
  reifyClause1 c :=
    let l := c.appFn!.appArg!
    let c := c.appArg!
    let (e₁, h₁) := reifyLiteral l
    if c.isConst then
      (e₁, mkApp4 (mkConst ``Sat.Clause.reify_one) v l e₁ h₁)
    else
      let (e₂, h₂) := reifyClause1 c
      (mkApp2 (mkConst ``And) e₁ e₂, mkApp7 (mkConst ``Sat.Clause.reify_and) v l e₁ c e₂ h₁ h₂)
  reifyLiteral l :=
    let n := l.appArg!
    let (e, h) := reifyVar n
    match l.appFn!.constName! with
    | ``Sat.Literal.pos =>
      (mkApp (mkConst ``Not) e, mkApp4 (mkConst ``Sat.Literal.reify_pos) v e n h)
    | ``Sat.Literal.neg =>
      (e, mkApp4 (mkConst ``Sat.Literal.reify_neg) v e n h)
    | _ => panic! "not a valid literal"
  reifyVar v :=
    let n := v.rawNatLit?.get!
    (mkBVar (2 * nvars - n), mkBVar (nvars - n - 1))
open Lean
namespace Parser
open Lean Std.Internal.Parsec String
def parseNat : String.Parser Nat := Json.Parser.natMaybeZero
def parseInt : String.Parser Int := do
  if (← peek!) = '-' then skip; pure <| -(← parseNat) else parseNat
partial def parseInts (arr : Array Int := #[]) : String.Parser (Array Int) := do
  match ← parseInt <* ws with
  | 0 => pure arr
  | n => parseInts (arr.push n)
partial def parseNats (arr : Array Nat := #[]) : String.Parser (Array Nat) := do
  match ← parseNat <* ws with
  | 0 => pure arr
  | n => parseNats (arr.push n)
def parseDimacs : String.Parser (Nat × Array (Array Int)) := do
  pstring "p cnf" *> ws
  let nvars ← parseNat <* ws
  let nclauses ← parseNat <* ws
  let mut clauses := Array.mkEmpty nclauses
  for _ in [:nclauses] do
    clauses := clauses.push (← parseInts)
  pure (nvars, clauses)
def parseLRAT : String.Parser (Array LRATStep) := many do
  let step ← parseNat <* ws
  if (← peek!) = 'd' then skip <* ws; pure <| LRATStep.del (← parseNats)
  else ws; pure <| LRATStep.add step (← parseInts) (← parseInts)
end Parser
open Std.Internal
def fromLRATAux (cnf lrat : String) (name : Name) : MetaM (Nat × Expr × Expr × Expr) := do
  let Parsec.ParseResult.success _ (nvars, arr) := Parser.parseDimacs cnf.mkIterator
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName ← mkAuxName (name ++ `ctx) 1
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type        := mkConst ``Sat.Fmla
    value       := ctx'
    hints       := ReducibilityHints.regular 0
    safety      := DefinitionSafety.safe
  }
  let ctx := mkConst ctxName
  let Parsec.ParseResult.success _ steps := Parser.parseLRAT lrat.mkIterator
    | throwError "parse LRAT failed"
  let proof ← buildProof arr ctx ctx' steps
  let declName ← mkAuxName (name ++ `proof) 1
  addDecl <| Declaration.thmDecl {
    name := declName
    levelParams := []
    type        := mkApp2 (mkConst ``Sat.Fmla.proof) ctx (buildClause #[])
    value       := proof
  }
  return (nvars, ctx, ctx', mkConst declName)
def fromLRAT (cnf lrat : String) (name : Name) : MetaM Unit := do
  let (nvars, ctx, ctx', proof) ← fromLRATAux cnf lrat name
  let (type, value) := buildReify ctx ctx' proof nvars
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }
open Elab Term
elab "lrat_proof " n:(ident <|> "example")
    ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ if n.1.isIdent then n.1.getId else `_example
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let go := do
      fromLRAT cnf lrat name
      withSaveInfoContext do
        Term.addTermInfo' n (mkConst name) (isBinder := true)
    if n.1.isIdent then go else withoutModifyingEnv go
lrat_proof example
  "p cnf 2 4
   1 2 0
   -1 2 0
   1 -2 0
   -1 -2 0"
  "5 -2 0 4 3 0
   5 d 3 4 0
   6 1 0 5 1 0
   6 d 1 0
   7 0 5 2 6 0"
elab "from_lrat " cnf:term:max ppSpace lrat:term:max : term => do
  let cnf ← unsafe evalTerm String (mkConst ``String) cnf
  let lrat ← unsafe evalTerm String (mkConst ``String) lrat
  let name ← mkAuxName `lrat
  fromLRAT cnf lrat name
  return mkConst name
example : ∀ (a b : Prop), (¬a ∧ ¬b ∨ a ∧ ¬b) ∨ ¬a ∧ b ∨ a ∧ b := from_lrat
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
end Sat
end Mathlib.Tactic