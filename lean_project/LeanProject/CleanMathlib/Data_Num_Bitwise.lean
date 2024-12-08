import Mathlib.Data.Num.Basic
import Mathlib.Data.Vector.Basic
open Mathlib
namespace PosNum
def lor : PosNum → PosNum → PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)
instance : OrOp PosNum where or := PosNum.lor
@[simp] lemma lor_eq_or (p q : PosNum) : p.lor q = p ||| q := rfl
def land : PosNum → PosNum → Num
  | 1, bit0 _ => 0
  | 1, _ => 1
  | bit0 _, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)
instance : HAnd PosNum PosNum Num where hAnd := PosNum.land
@[simp] lemma land_eq_and (p q : PosNum) : p.land q = p &&& q := rfl
def ldiff : PosNum → PosNum → Num
  | 1, bit0 _ => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)
def lxor : PosNum → PosNum → Num
  | 1, 1 => 0
  | 1, bit0 q => Num.pos (bit1 q)
  | 1, bit1 q => Num.pos (bit0 q)
  | bit0 p, 1 => Num.pos (bit1 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (lxor p q)
  | bit0 p, bit1 q => Num.bit1 (lxor p q)
  | bit1 p, bit0 q => Num.bit1 (lxor p q)
  | bit1 p, bit1 q => Num.bit0 (lxor p q)
instance : HXor PosNum PosNum Num where hXor := PosNum.lxor
@[simp] lemma lxor_eq_xor (p q : PosNum) : p.lxor q = p ^^^ q := rfl
def testBit : PosNum → Nat → Bool
  | 1, 0 => true
  | 1, _ => false
  | bit0 _, 0 => false
  | bit0 p, n + 1 => testBit p n
  | bit1 _, 0 => true
  | bit1 p, n + 1 => testBit p n
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => oneBits p (d + 1)
  | bit1 p, d => d :: oneBits p (d + 1)
def shiftl : PosNum → Nat → PosNum
  | p, 0 => p
  | p, n + 1 => shiftl p.bit0 n
instance : HShiftLeft PosNum Nat PosNum where hShiftLeft := PosNum.shiftl
@[simp] lemma shiftl_eq_shiftLeft (p : PosNum) (n : Nat) : p.shiftl n = p <<< n := rfl
theorem shiftl_succ_eq_bit0_shiftl : ∀ (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)
  | _, 0       => rfl
  | p, .succ n => shiftl_succ_eq_bit0_shiftl p.bit0 n
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, _ => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n
instance : HShiftRight PosNum Nat Num where hShiftRight := PosNum.shiftr
@[simp] lemma shiftr_eq_shiftRight (p : PosNum) (n : Nat) : p.shiftr n = p >>> n := rfl
end PosNum
namespace Num
protected def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => pos (p ||| q)
instance : OrOp Num where or := Num.lor
@[simp] lemma lor_eq_or (p q : Num) : p.lor q = p ||| q := rfl
def land : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => p &&& q
instance : AndOp Num where and := Num.land
@[simp] lemma land_eq_and (p q : Num) : p.land q = p &&& q := rfl
def ldiff : Num → Num → Num
  | 0, _ => 0
  | p, 0 => p
  | pos p, pos q => p.ldiff q
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => p ^^^ q
instance : Xor Num where xor := Num.lxor
@[simp] lemma lxor_eq_xor (p q : Num) : p.lxor q = p ^^^ q := rfl
def shiftl : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => pos (p <<< n)
instance : HShiftLeft Num Nat Num where hShiftLeft := Num.shiftl
@[simp] lemma shiftl_eq_shiftLeft (p : Num) (n : Nat) : p.shiftl n = p <<< n := rfl
def shiftr : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => p >>> n
instance : HShiftRight Num Nat Num where hShiftRight := Num.shiftr
@[simp] lemma shiftr_eq_shiftRight (p : Num) (n : Nat) : p.shiftr n = p >>> n := rfl
def testBit : Num → Nat → Bool
  | 0, _ => false
  | pos p, n => p.testBit n
def oneBits : Num → List Nat
  | 0 => []
  | pos p => p.oneBits 0
end Num
inductive NzsNum : Type
  | msb : Bool → NzsNum
  | bit : Bool → NzsNum → NzsNum
  deriving DecidableEq  
inductive SNum : Type
  | zero : Bool → SNum
  | nz : NzsNum → SNum
  deriving DecidableEq  
instance : Coe NzsNum SNum :=
  ⟨SNum.nz⟩
instance : Zero SNum :=
  ⟨SNum.zero false⟩
instance : One NzsNum :=
  ⟨NzsNum.msb true⟩
instance : One SNum :=
  ⟨SNum.nz 1⟩
instance : Inhabited NzsNum :=
  ⟨1⟩
instance : Inhabited SNum :=
  ⟨0⟩
namespace NzsNum
@[inherit_doc]
scoped notation a "::" b => bit a b
def sign : NzsNum → Bool
  | msb b => not b
  | _ :: p => sign p
@[match_pattern]
def not : NzsNum → NzsNum
  | msb b => msb (Not b)
  | b :: p => Not b :: not p
@[inherit_doc]
scoped prefix:100 "~" => not
def bit0 : NzsNum → NzsNum :=
  bit false
def bit1 : NzsNum → NzsNum :=
  bit true
def head : NzsNum → Bool
  | msb b => b
  | b :: _ => b
def tail : NzsNum → SNum
  | msb b => SNum.zero (Not b)
  | _ :: p => p
end NzsNum
namespace SNum
open NzsNum
def sign : SNum → Bool
  | zero z => z
  | nz p => p.sign
@[match_pattern]
def not : SNum → SNum
  | zero z => zero (Not z)
  | nz p => ~p
@[inherit_doc]
scoped prefix:100 (priority := default + 1) "~" => not
@[match_pattern]
def bit : Bool → SNum → SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b
@[inherit_doc]
scoped notation a "::" b => bit a b
def bit0 : SNum → SNum :=
  bit false
def bit1 : SNum → SNum :=
  bit true
theorem bit_zero (b : Bool) : (b :: zero b) = zero b := by cases b <;> rfl
theorem bit_one (b : Bool) : (b :: zero (Not b)) = msb b := by cases b <;> rfl
end SNum
namespace NzsNum
open SNum
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) :
    ∀ p : NzsNum, C p
  | msb b => by rw [← bit_one]; exact s b (SNum.zero (Not b)) (z (Not b))
  | bit b p => s b p (drec' z s p)
end NzsNum
namespace SNum
open NzsNum
def head : SNum → Bool
  | zero z => z
  | nz p => p.head
def tail : SNum → SNum
  | zero z => zero z
  | nz p => p.tail
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s
def rec' {α} (z : Bool → α) (s : Bool → SNum → α → α) : SNum → α :=
  drec' z s
def testBit : Nat → SNum → Bool
  | 0, p => head p
  | n + 1, p => testBit n (tail p)
def succ : SNum → SNum :=
  rec' (fun b ↦ cond b 0 1) fun b p succp ↦ cond b (false :: succp) (true :: p)
def pred : SNum → SNum :=
  rec' (fun b ↦ cond b (~1) (~0)) fun b p predp ↦ cond b (false :: p) (true :: predp)
protected def neg (n : SNum) : SNum :=
  succ (~n)
instance : Neg SNum :=
  ⟨SNum.neg⟩
def czAdd : Bool → Bool → SNum → SNum
  | false, false, p => p
  | false, true, p => pred p
  | true, false, p => succ p
  | true, true, p => p
end SNum
namespace SNum
def bits : SNum → ∀ n, Mathlib.Vector Bool n
  | _, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n
def cAdd : SNum → SNum → Bool → SNum :=
  rec' (fun a p c ↦ czAdd c a p) fun a p IH ↦
    rec' (fun b c ↦ czAdd c b (a :: p)) fun b q _ c ↦ Bool.xor3 a b c :: IH q (Bool.carry a b c)
protected def add (a b : SNum) : SNum :=
  cAdd a b false
instance : Add SNum :=
  ⟨SNum.add⟩
protected def sub (a b : SNum) : SNum :=
  a + -b
instance : Sub SNum :=
  ⟨SNum.sub⟩
protected def mul (a : SNum) : SNum → SNum :=
  rec' (fun b ↦ cond b (-a) 0) fun b _ IH ↦ cond b (bit0 IH + a) (bit0 IH)
instance : Mul SNum :=
  ⟨SNum.mul⟩
end SNum