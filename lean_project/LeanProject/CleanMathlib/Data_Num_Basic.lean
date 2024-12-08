import Lean.Linter.Deprecated
import Mathlib.Algebra.Group.ZeroOne
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic.TypeStar
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving DecidableEq
instance : One PosNum :=
  ⟨PosNum.one⟩
instance : Inhabited PosNum :=
  ⟨1⟩
inductive Num : Type
  | zero : Num
  | pos : PosNum → Num
  deriving DecidableEq
instance : Zero Num :=
  ⟨Num.zero⟩
instance : One Num :=
  ⟨Num.pos 1⟩
instance : Inhabited Num :=
  ⟨0⟩
inductive ZNum : Type
  | zero : ZNum
  | pos : PosNum → ZNum
  | neg : PosNum → ZNum
  deriving DecidableEq
instance : Zero ZNum :=
  ⟨ZNum.zero⟩
instance : One ZNum :=
  ⟨ZNum.pos 1⟩
instance : Inhabited ZNum :=
  ⟨0⟩
namespace PosNum
def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0
def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n
def isOne : PosNum → Bool
  | 1 => true
  | _ => false
protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (PosNum.add a b)
  | bit1 a, bit1 b => bit0 (succ (PosNum.add a b))
  | bit0 a, bit1 b => bit1 (PosNum.add a b)
  | bit1 a, bit0 b => bit1 (PosNum.add a b)
instance : Add PosNum :=
  ⟨PosNum.add⟩
def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id
def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)
def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (natSize n)
  | bit1 n => Nat.succ (natSize n)
protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (PosNum.mul a b)
  | bit1 b => bit0 (PosNum.mul a b) + a
instance : Mul PosNum :=
  ⟨PosNum.mul⟩
def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (ofNatSucc n)
def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)
instance {n : ℕ} : OfNat PosNum (n + 1) where
  ofNat := ofNat (n + 1)
open Ordering
def cmp : PosNum → PosNum → Ordering
  | 1, 1 => eq
  | _, 1 => gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt gt gt
  | bit1 a, bit1 b => cmp a b
instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩
instance decidableLT : @DecidableRel PosNum (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance
instance decidableLE : @DecidableRel PosNum (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance
end PosNum
section
variable {α : Type*} [One α] [Add α]
@[coe]
def castPosNum : PosNum → α
  | 1 => 1
  | PosNum.bit0 a => castPosNum a + castPosNum a
  | PosNum.bit1 a => castPosNum a + castPosNum a + 1
@[coe]
def castNum [Zero α] : Num → α
  | 0 => 0
  | Num.pos p => castPosNum p
instance (priority := 900) posNumCoe : CoeHTCT PosNum α :=
  ⟨castPosNum⟩
instance (priority := 900) numNatCoe [Zero α] : CoeHTCT Num α :=
  ⟨castNum⟩
instance : Repr PosNum :=
  ⟨fun n _ => repr (n : ℕ)⟩
instance : Repr Num :=
  ⟨fun n _ => repr (n : ℕ)⟩
end
namespace Num
open PosNum
def succ' : Num → PosNum
  | 0 => 1
  | pos p => succ p
def succ (n : Num) : Num :=
  pos (succ' n)
protected def add : Num → Num → Num
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
instance : Add Num :=
  ⟨Num.add⟩
protected def bit0 : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)
protected def bit1 : Num → Num
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)
def bit (b : Bool) : Num → Num :=
  cond b Num.bit1 Num.bit0
def size : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.size n)
def natSize : Num → Nat
  | 0 => 0
  | pos n => PosNum.natSize n
protected def mul : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
instance : Mul Num :=
  ⟨Num.mul⟩
open Ordering
def cmp : Num → Num → Ordering
  | 0, 0 => eq
  | _, 0 => gt
  | 0, _ => lt
  | pos a, pos b => PosNum.cmp a b
instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
instance : LE Num :=
  ⟨fun a b => ¬b < a⟩
instance decidableLT : @DecidableRel Num (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance
instance decidableLE : @DecidableRel Num (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance
def toZNum : Num → ZNum
  | 0 => 0
  | pos a => ZNum.pos a
def toZNumNeg : Num → ZNum
  | 0 => 0
  | pos a => ZNum.neg a
def ofNat' : ℕ → Num :=
  Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)
end Num
namespace ZNum
open PosNum
def zNeg : ZNum → ZNum
  | 0 => 0
  | pos a => neg a
  | neg a => pos a
instance : Neg ZNum :=
  ⟨zNeg⟩
def abs : ZNum → Num
  | 0 => 0
  | pos a => Num.pos a
  | neg a => Num.pos a
def succ : ZNum → ZNum
  | 0 => 1
  | pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZNumNeg
def pred : ZNum → ZNum
  | 0 => neg 1
  | pos a => (PosNum.pred' a).toZNum
  | neg a => neg (PosNum.succ a)
protected def bit0 : ZNum → ZNum
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)
protected def bit1 : ZNum → ZNum
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)
protected def bitm1 : ZNum → ZNum
  | 0 => neg 1
  | pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)
def ofInt' : ℤ → ZNum
  | Int.ofNat n => Num.toZNum (Num.ofNat' n)
  | Int.negSucc n => Num.toZNumNeg (Num.ofNat' (n + 1))
end ZNum
namespace PosNum
open ZNum
def sub' : PosNum → PosNum → ZNum
  | a, 1 => (pred' a).toZNum
  | 1, b => (pred' b).toZNumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0
def ofZNum' : ZNum → Option PosNum
  | ZNum.pos p => some p
  | _ => none
def ofZNum : ZNum → PosNum
  | ZNum.pos p => p
  | _ => 1
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | ZNum.pos p => p
  | _ => 1
instance : Sub PosNum :=
  ⟨PosNum.sub⟩
end PosNum
namespace Num
def ppred : Num → Option Num
  | 0 => none
  | pos p => some p.pred'
def pred : Num → Num
  | 0 => 0
  | pos p => p.pred'
def div2 : Num → Num
  | 0 => 0
  | 1 => 0
  | pos (PosNum.bit0 p) => pos p
  | pos (PosNum.bit1 p) => pos p
def ofZNum' : ZNum → Option Num
  | 0 => some 0
  | ZNum.pos p => some (pos p)
  | ZNum.neg _ => none
def ofZNum : ZNum → Num
  | ZNum.pos p => pos p
  | _ => 0
def sub' : Num → Num → ZNum
  | 0, 0 => 0
  | pos a, 0 => ZNum.pos a
  | 0, pos b => ZNum.neg b
  | pos a, pos b => a.sub' b
def psub (a b : Num) : Option Num :=
  ofZNum' (sub' a b)
protected def sub (a b : Num) : Num :=
  ofZNum (sub' a b)
instance : Sub Num :=
  ⟨Num.sub⟩
end Num
namespace ZNum
open PosNum
protected def add : ZNum → ZNum → ZNum
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
  | pos a, neg b => sub' a b
  | neg a, pos b => sub' b a
  | neg a, neg b => neg (a + b)
instance : Add ZNum :=
  ⟨ZNum.add⟩
protected def mul : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
  | pos a, neg b => neg (a * b)
  | neg a, pos b => neg (a * b)
  | neg a, neg b => pos (a * b)
instance : Mul ZNum :=
  ⟨ZNum.mul⟩
open Ordering
def cmp : ZNum → ZNum → Ordering
  | 0, 0 => eq
  | pos a, pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | pos _, _ => gt
  | neg _, _ => lt
  | _, pos _ => lt
  | _, neg _ => gt
instance : LT ZNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩
instance : LE ZNum :=
  ⟨fun a b => ¬b < a⟩
instance decidableLT : @DecidableRel ZNum (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance
instance decidableLE : @DecidableRel ZNum (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance
end ZNum
namespace PosNum
def divModAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)
def divMod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1
def div' (n d : PosNum) : Num :=
  (divMod d n).1
def mod' (n d : PosNum) : Num :=
  (divMod d n).2
private def sqrtAux1 (b : PosNum) (r n : Num) : Num × Num :=
  match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)
private def sqrtAux : PosNum → Num → Num → Num
  | b@(bit0 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1           => fun r n => (sqrtAux1 1 r n).1
end PosNum
namespace Num
def div : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => PosNum.div' n d
def mod : Num → Num → Num
  | 0, _ => 0
  | n, 0 => n
  | pos n, pos d => PosNum.mod' n d
instance : Div Num :=
  ⟨Num.div⟩
instance : Mod Num :=
  ⟨Num.mod⟩
def gcdAux : Nat → Num → Num → Num
  | 0, _, b => b
  | Nat.succ _, 0, b => b
  | Nat.succ n, a, b => gcdAux n (b % a) a
def gcd (a b : Num) : Num :=
  if a ≤ b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a
end Num
namespace ZNum
def div : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => Num.toZNum (PosNum.div' n d)
  | pos n, neg d => Num.toZNumNeg (PosNum.div' n d)
  | neg n, pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'
def mod : ZNum → ZNum → ZNum
  | 0, _ => 0
  | pos n, d => Num.toZNum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ
instance : Div ZNum :=
  ⟨ZNum.div⟩
instance : Mod ZNum :=
  ⟨ZNum.mod⟩
def gcd (a b : ZNum) : Num :=
  a.abs.gcd b.abs
end ZNum
section
variable {α : Type*} [Zero α] [One α] [Add α] [Neg α]
@[coe]
def castZNum : ZNum → α
  | 0 => 0
  | ZNum.pos p => p
  | ZNum.neg p => -p
instance (priority := 900) znumCoe : CoeHTCT ZNum α :=
  ⟨castZNum⟩
instance : Repr ZNum :=
  ⟨fun n _ => repr (n : ℤ)⟩
end