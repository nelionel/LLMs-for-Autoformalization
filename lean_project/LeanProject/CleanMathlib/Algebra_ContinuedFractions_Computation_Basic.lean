import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.ContinuedFractions.Basic
assert_not_exists Finset
namespace GenContFract
variable (K : Type*)
structure IntFractPair where
  b : ℤ
  fr : K
variable {K}
namespace IntFractPair
instance [Repr K] : Repr (IntFractPair K) :=
  ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩
instance inhabited [Inhabited K] : Inhabited (IntFractPair K) :=
  ⟨⟨0, default⟩⟩
def mapFr {β : Type*} (f : K → β) (gp : IntFractPair K) : IntFractPair β :=
  ⟨gp.b, f gp.fr⟩
section coe
variable {β : Type*} [Coe K β]
@[coe]
def coeFn : IntFractPair K → IntFractPair β := mapFr (↑)
instance coe : Coe (IntFractPair K) (IntFractPair β) where
  coe := coeFn
@[simp, norm_cast]
theorem coe_to_intFractPair {b : ℤ} {fr : K} :
    (↑(IntFractPair.mk b fr) : IntFractPair β) = IntFractPair.mk b (↑fr : β) :=
  rfl
end coe
variable [LinearOrderedField K] [FloorRing K]
protected def of (v : K) : IntFractPair K :=
  ⟨⌊v⌋, Int.fract v⟩
protected def stream (v : K) : Stream' <| Option (IntFractPair K)
  | 0 => some (IntFractPair.of v)
  | n + 1 =>
    (IntFractPair.stream v n).bind fun ap_n =>
      if ap_n.fr = 0 then none else some (IntFractPair.of ap_n.fr⁻¹)
theorem stream_isSeq (v : K) : (IntFractPair.stream v).IsSeq := by
  intro _ hyp
  simp [IntFractPair.stream, hyp]
protected def seq1 (v : K) : Stream'.Seq1 <| IntFractPair K :=
  ⟨IntFractPair.of v, 
    Stream'.Seq.tail
      ⟨IntFractPair.stream v, 
        @stream_isSeq _ _ _ v⟩⟩ 
end IntFractPair
protected def of [LinearOrderedField K] [FloorRing K] (v : K) : GenContFract K :=
  let ⟨h, s⟩ := IntFractPair.seq1 v 
  ⟨h.b, 
    s.map fun p => ⟨1, p.b⟩⟩ 
end GenContFract