import Lean.Meta.Basic
import Mathlib.Init
open Lean Meta
namespace Mathlib.Tactic
namespace BicategoryLike
structure Obj where
  e? : Option Expr
  deriving Inhabited
def Obj.e (a : Obj) : Expr :=
  a.e?.get!
structure Atom₁ : Type where
  e : Expr
  src : Obj
  tgt : Obj
  deriving Inhabited
class MkAtom₁ (m : Type → Type) where
  ofExpr (e : Expr) : m Atom₁
inductive Mor₁ : Type
  | id (e : Expr) (a : Obj) : Mor₁
  | comp (e : Expr) : Mor₁ → Mor₁ → Mor₁
  | of : Atom₁ → Mor₁
  deriving Inhabited
class MkMor₁ (m : Type → Type) where
  ofExpr (e : Expr) : m Mor₁
def Mor₁.e : Mor₁ → Expr
  | .id e _ => e
  | .comp e _ _ => e
  | .of a => a.e
def Mor₁.src : Mor₁ → Obj
  | .id _ a => a
  | .comp _ f _ => f.src
  | .of f => f.src
def Mor₁.tgt : Mor₁ → Obj
  | .id _ a => a
  | .comp _ _ g => g.tgt
  | .of f => f.tgt
def Mor₁.toList : Mor₁ → List Atom₁
  | .id _ _ => []
  | .comp _ f g => f.toList ++ g.toList
  | .of f => [f]
class MonadMor₁ (m : Type → Type) where
  id₁M (a : Obj) : m Mor₁
  comp₁M (f g : Mor₁) : m Mor₁
structure CoherenceHom where
  e : Expr
  src : Mor₁
  tgt : Mor₁
  inst : Expr
  unfold : Expr
  deriving Inhabited
structure AtomIso where
  e : Expr
  src : Mor₁
  tgt : Mor₁
  deriving Inhabited
inductive StructuralAtom : Type
  | associator (e : Expr) (f g h : Mor₁) : StructuralAtom
  | leftUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  | rightUnitor (e : Expr) (f : Mor₁) : StructuralAtom
  | id (e : Expr) (f : Mor₁) : StructuralAtom
  | coherenceHom (α : CoherenceHom) : StructuralAtom
  deriving Inhabited
inductive Mor₂Iso : Type where
  | structuralAtom (α : StructuralAtom) : Mor₂Iso
  | comp (e : Expr) (f g h : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | whiskerLeft (e : Expr) (f g h : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | whiskerRight (e : Expr) (f g : Mor₁) (η : Mor₂Iso) (h : Mor₁) : Mor₂Iso
  | horizontalComp (e : Expr) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂Iso) : Mor₂Iso
  | inv (e : Expr) (f g : Mor₁) (η : Mor₂Iso) : Mor₂Iso
  | coherenceComp (e : Expr) (f g h i : Mor₁) (α : CoherenceHom) (η θ : Mor₂Iso) : Mor₂Iso
  | of (η : AtomIso) : Mor₂Iso
  deriving Inhabited
class MonadCoherehnceHom (m : Type → Type) where
  unfoldM (α : CoherenceHom) : m Mor₂Iso
def StructuralAtom.e : StructuralAtom → Expr
  | .associator e .. => e
  | .leftUnitor e .. => e
  | .rightUnitor e .. => e
  | .id e .. => e
  | .coherenceHom α => α.e
open MonadMor₁
variable {m : Type → Type} [Monad m]
def StructuralAtom.srcM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M (← comp₁M f g) h
  | .leftUnitor _ f => do comp₁M (← id₁M f.src) f
  | .rightUnitor _ f => do comp₁M f (← id₁M f.tgt)
  | .id _ f => return f
  | .coherenceHom α => return α.src
def StructuralAtom.tgtM [MonadMor₁ m] : StructuralAtom → m Mor₁
  | .associator _ f g h => do comp₁M f (← comp₁M g h)
  | .leftUnitor _ f => return f
  | .rightUnitor _ f => return f
  | .id _ f => return f
  | .coherenceHom α => return α.tgt
def Mor₂Iso.e : Mor₂Iso → Expr
  | .structuralAtom α => α.e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .inv e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e
def Mor₂Iso.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.srcM
  | .comp _ f .. => return f
  | .whiskerLeft _ f g .. => do comp₁M f g
  | .whiskerRight _ f _ _ h => do comp₁M f h
  | .horizontalComp _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .inv _ _ g _ => return g
  | .coherenceComp _ f .. => return f
  | .of η => return η.src
def Mor₂Iso.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂Iso → m Mor₁
  | .structuralAtom α => α.tgtM
  | .comp _ _ _ h .. => return h
  | .whiskerLeft _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .inv _ f _ _ => return f
  | .coherenceComp _ _ _ _ i .. => return i
  | .of η => return η.tgt
class MonadMor₂Iso (m : Type → Type) where
  associatorM (f g h : Mor₁) : m StructuralAtom
  leftUnitorM (f : Mor₁) : m StructuralAtom
  rightUnitorM (f : Mor₁) : m StructuralAtom
  id₂M (f : Mor₁) : m StructuralAtom
  coherenceHomM (f g : Mor₁) (inst : Expr) : m CoherenceHom
  comp₂M (η θ : Mor₂Iso) : m Mor₂Iso
  whiskerLeftM (f : Mor₁) (η : Mor₂Iso) : m Mor₂Iso
  whiskerRightM (η : Mor₂Iso) (h : Mor₁) : m Mor₂Iso
  horizontalCompM (η θ : Mor₂Iso) : m Mor₂Iso
  symmM (η : Mor₂Iso) : m Mor₂Iso
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂Iso) : m Mor₂Iso
namespace MonadMor₂Iso
variable {m : Type → Type} [Monad m] [MonadMor₂Iso m]
def associatorM' (f g h : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.associatorM f g h
def leftUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.leftUnitorM f
def rightUnitorM' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.rightUnitorM f
def id₂M' (f : Mor₁) : m Mor₂Iso := do
  return .structuralAtom <| ← MonadMor₂Iso.id₂M f
def coherenceHomM' (f g : Mor₁) (inst : Expr) : m Mor₂Iso := do
  return .structuralAtom <| .coherenceHom <| ← MonadMor₂Iso.coherenceHomM f g inst
end MonadMor₂Iso
structure Atom where
  e : Expr
  src : Mor₁
  tgt : Mor₁
  deriving Inhabited
structure IsoLift where
  e : Mor₂Iso
  eq : Expr
inductive Mor₂ : Type where
  | isoHom (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  | isoInv (e : Expr) (isoLift : IsoLift) (iso : Mor₂Iso) : Mor₂
  | id (e : Expr) (isoLift : IsoLift) (f : Mor₁) : Mor₂
  | comp (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η θ : Mor₂) : Mor₂
  | whiskerLeft (e : Expr) (isoLift? : Option IsoLift) (f g h : Mor₁) (η : Mor₂) : Mor₂
  | whiskerRight (e : Expr) (isoLift? : Option IsoLift) (f g : Mor₁) (η : Mor₂) (h : Mor₁) : Mor₂
  | horizontalComp (e : Expr) (isoLift? : Option IsoLift) (f₁ g₁ f₂ g₂ : Mor₁) (η θ : Mor₂) : Mor₂
  | coherenceComp (e : Expr) (isoLift? : Option IsoLift) (f g h i : Mor₁)
    (α : CoherenceHom) (η θ : Mor₂) : Mor₂
  | of (η : Atom) : Mor₂
  deriving Inhabited
class MkMor₂ (m : Type → Type) where
  ofExpr (e : Expr) : m Mor₂
def Mor₂.e : Mor₂ → Expr
  | .isoHom e .. => e
  | .isoInv e .. => e
  | .id e .. => e
  | .comp e .. => e
  | .whiskerLeft e .. => e
  | .whiskerRight e .. => e
  | .horizontalComp e .. => e
  | .coherenceComp e .. => e
  | .of η => η.e
def Mor₂.isoLift? : Mor₂ → Option IsoLift
  | .isoHom _ isoLift .. => some isoLift
  | .isoInv _ isoLift .. => some isoLift
  | .id _ isoLift .. => some isoLift
  | .comp _ isoLift? .. => isoLift?
  | .whiskerLeft _ isoLift? .. => isoLift?
  | .whiskerRight _ isoLift? .. => isoLift?
  | .horizontalComp _ isoLift? .. => isoLift?
  | .coherenceComp _ isoLift? .. => isoLift?
  | .of _ => none
def Mor₂.srcM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.srcM
  | .isoInv _ _ iso => iso.tgtM
  | .id _ _ f => return f
  | .comp _ _ f .. => return f
  | .whiskerLeft _ _ f g .. => do comp₁M f g
  | .whiskerRight _ _ f _ _ h => do comp₁M f h
  | .horizontalComp _ _ f₁ _ f₂ .. => do comp₁M f₁ f₂
  | .coherenceComp _ _ f .. => return f
  | .of η => return η.src
def Mor₂.tgtM {m : Type → Type} [Monad m] [MonadMor₁ m] : Mor₂ → m Mor₁
  | .isoHom _ _ iso => iso.tgtM
  | .isoInv _ _ iso => iso.srcM
  | .id _ _ f => return f
  | .comp _ _ _ _ h .. => return h
  | .whiskerLeft _ _ f _ h _ => do comp₁M f h
  | .whiskerRight _ _ _ g _ h => do comp₁M g h
  | .horizontalComp _ _ _ g₁ _ g₂ _ _ => do comp₁M g₁ g₂
  | .coherenceComp _ _ _ _ _ i .. => return i
  | .of η => return η.tgt
class MonadMor₂ (m : Type → Type) where
  homM (η : Mor₂Iso) : m Mor₂
  atomHomM (η : AtomIso) : m Atom
  invM (η : Mor₂Iso) : m Mor₂
  atomInvM (η : AtomIso) : m Atom
  id₂M (f : Mor₁) : m Mor₂
  comp₂M (η θ : Mor₂) : m Mor₂
  whiskerLeftM (f : Mor₁) (η : Mor₂) : m Mor₂
  whiskerRightM (η : Mor₂) (h : Mor₁) : m Mor₂
  horizontalCompM (η θ : Mor₂) : m Mor₂
  coherenceCompM (α : CoherenceHom) (η θ : Mor₂) : m Mor₂
inductive NormalizedHom : Type
  | nil (e : Mor₁) (a : Obj) : NormalizedHom
  | cons (e : Mor₁) : NormalizedHom → Atom₁ → NormalizedHom
  deriving Inhabited
def NormalizedHom.e : NormalizedHom → Mor₁
  | NormalizedHom.nil e _ => e
  | NormalizedHom.cons e _ _  => e
def NormalizedHom.src : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ p _ => p.src
def NormalizedHom.tgt : NormalizedHom → Obj
  | NormalizedHom.nil _ a => a
  | NormalizedHom.cons _ _  f => f.tgt
def normalizedHom.nilM [MonadMor₁ m] (a : Obj) : m NormalizedHom := do
  return NormalizedHom.nil (← id₁M a) a
def NormalizedHom.consM [MonadMor₁ m] (p : NormalizedHom) (f : Atom₁) :
    m NormalizedHom := do
  return NormalizedHom.cons (← comp₁M p.e (.of f)) p f
class Context (ρ : Type) where
  mkContext? : Expr → MetaM (Option ρ)
export Context (mkContext?)
def mkContext {ρ  : Type} [Context ρ] (e : Expr) : MetaM ρ := do
  match ← mkContext? e with
  | some c => return c
  | none => throwError "failed to construct a monoidal category or bicategory context from {e}"
structure State where
  cache : PersistentExprMap Mor₁ := {}
abbrev CoherenceM (ρ : Type) := ReaderT ρ <| StateT State MetaM
def CoherenceM.run {α ρ : Type} (x : CoherenceM ρ α) (ctx : ρ) (s : State := {}) :
    MetaM α := do
  Prod.fst <$> ReaderT.run x ctx s
end BicategoryLike
end Tactic
end Mathlib