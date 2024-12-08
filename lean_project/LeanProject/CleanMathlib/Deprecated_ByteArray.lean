import Batteries.Data.ByteSubarray 
import Mathlib.Init
set_option linter.deprecated false
namespace Nat
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def Up (ub a i : Nat) := i < a ∧ i < ub
theorem Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩
theorem Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := (measure (ub - ·)).wf) fun ⟨ia, iu⟩ ↦ Nat.sub_lt_sub_left iu ia
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def upRel (ub : Nat) : WellFoundedRelation Nat := ⟨Up ub, Up.WF ub⟩
end Nat
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
structure ByteSliceT := (arr : ByteArray) (off : Nat)
namespace ByteSliceT
@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off
@[inline] def getOp (self : ByteSliceT) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)
end ByteSliceT
def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0⟩
@[deprecated Batteries.ByteSubarray (since := "2024-08-19")]
structure ByteSlice := (arr : ByteArray) (off len : Nat)
namespace ByteSlice
def toArray : ByteSlice → ByteArray
  | ⟨arr, off, len⟩ => arr.extract off len
@[inline] def getOp (self : ByteSlice) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)
universe u v
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def forIn.loop {m : Type u → Type v} {β : Type u} [Monad m] (f : UInt8 → β → m (ForInStep β))
    (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if h : i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => have := Nat.Up.next h; loop f arr off _end (i+1) b
  else pure b
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
instance {m : Type u → Type v} : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f ↦ forIn.loop f arr off (off + len) off b⟩
end ByteSlice
def ByteSliceT.toSlice : ByteSliceT → ByteSlice
  | ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩
def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩
def ByteSlice.toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do s := s.push (Char.ofUInt8 c)
  s
instance : ToString ByteSlice where
  toString bs := Id.run do
    let mut s := ""
    for c in bs do s := s.push (Char.ofUInt8 c)
    s