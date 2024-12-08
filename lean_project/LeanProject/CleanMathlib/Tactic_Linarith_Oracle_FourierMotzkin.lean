import Mathlib.Std.Data.HashMap
import Batteries.Lean.HashMap
import Mathlib.Tactic.Linarith.Datatypes
open Batteries
open Std (format ToFormat)
namespace Linarith
inductive CompSource : Type
  | assump : Nat → CompSource
  | add : CompSource → CompSource → CompSource
  | scale : Nat → CompSource → CompSource
deriving Inhabited
def CompSource.flatten : CompSource → Std.HashMap Nat Nat
  | (CompSource.assump n) => Std.HashMap.empty.insert n 1
  | (CompSource.add c1 c2) =>
      (CompSource.flatten c1).mergeWith (fun _ b b' => b + b') (CompSource.flatten c2)
  | (CompSource.scale n c) => (CompSource.flatten c).mapVal (fun _ v => v * n)
def CompSource.toString : CompSource → String
  | (CompSource.assump e) => ToString.toString e
  | (CompSource.add c1 c2) => CompSource.toString c1 ++ " + " ++ CompSource.toString c2
  | (CompSource.scale n c) => ToString.toString n ++ " * " ++ CompSource.toString c
instance : ToFormat CompSource :=
  ⟨fun a => CompSource.toString a⟩
structure PComp : Type where
  c : Comp
  src : CompSource
  history : RBSet ℕ Ord.compare
  effective : RBSet ℕ Ord.compare
  implicit : RBSet ℕ Ord.compare
  vars : RBSet ℕ Ord.compare
def PComp.maybeMinimal (c : PComp) (elimedGE : ℕ) : Bool :=
  c.history.size ≤ 1 + ((c.implicit.filter (· ≥ elimedGE)).union c.effective).size
def PComp.cmp (p1 p2 : PComp) : Ordering := p1.c.cmp p2.c
def PComp.scale (c : PComp) (n : ℕ) : PComp :=
  { c with c := c.c.scale n, src := c.src.scale n }
def PComp.add (c1 c2 : PComp) (elimVar : ℕ) : PComp :=
  let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.sdiff (.ofList c.vars _)).sdiff effective
  ⟨c, src, history, effective, implicit, vars⟩
def PComp.assump (c : Comp) (n : ℕ) : PComp where
  c := c
  src := CompSource.assump n
  history := RBSet.empty.insert n
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _
instance : ToFormat PComp :=
  ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩
instance : ToString PComp :=
  ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩
abbrev PCompSet := RBSet PComp PComp.cmp
def elimVar (c1 c2 : Comp) (a : ℕ) : Option (ℕ × ℕ) :=
  let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none
def pelimVar (p1 p2 : PComp) (a : ℕ) : Option PComp := do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a
def PComp.isContr (p : PComp) : Bool := p.c.isContr
def elimWithSet (a : ℕ) (p : PComp) (comps : PCompSet) : PCompSet :=
  comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) RBSet.empty
structure LinarithData : Type where
  maxVar : ℕ
  comps : PCompSet
abbrev LinarithM : Type → Type :=
  StateT LinarithData (ExceptT PComp Lean.Core.CoreM)
def getMaxVar : LinarithM ℕ :=
  LinarithData.maxVar <$> get
def getPCompSet : LinarithM PCompSet :=
  LinarithData.comps <$> get
def validate : LinarithM Unit := do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c
def update (maxVar : ℕ) (comps : PCompSet) : LinarithM Unit := do
  StateT.set ⟨maxVar, comps⟩
  validate
def splitSetByVarSign (a : ℕ) (comps : PCompSet) : PCompSet × PCompSet × PCompSet :=
  comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨RBSet.empty, RBSet.empty, RBSet.empty⟩
def elimVarM (a : ℕ) : LinarithM Unit := do
  let vs ← getMaxVar
  if (a ≤ vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      pure (s.union (elimWithSet a p neg))) notPresent)
  else
    pure ()
def elimAllVarsM : LinarithM Unit := do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i
def mkLinarithData (hyps : List Comp) (maxVar : ℕ) : LinarithData :=
  ⟨maxVar, .ofList (hyps.enum.map fun ⟨n, cmp⟩ => PComp.assump cmp n) _⟩
def CertificateOracle.fourierMotzkin : CertificateOracle where
  produceCertificate hyps maxVar :=  do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) : _)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten
end Linarith