import Mathlib.Data.Seq.Seq
import Mathlib.Algebra.Field.Defs
variable (α : Type*)
structure GenContFract.Pair where
  a : α
  b : α
  deriving Inhabited
open GenContFract
namespace GenContFract.Pair
variable {α}
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ ↦ "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩
def map {β : Type*} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩
section coe
variable {β : Type*} [Coe α β]
@[coe]
def coeFn : Pair α → Pair β := map (↑)
instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩
@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl
end coe
end GenContFract.Pair
@[ext]
structure GenContFract where
  h : α
  s : Stream'.Seq <| Pair α
variable {α}
namespace GenContFract
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩
instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩
def partNums (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.a
def partDens (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.b
def TerminatedAt (g : GenContFract α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n
instance terminatedAtDecidable (g : GenContFract α) (n : ℕ) :
    Decidable (g.TerminatedAt n) := by
  unfold TerminatedAt
  infer_instance
def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates
section coe
variable {β : Type*} [Coe α β]
@[coe]
def coeFn : GenContFract α → GenContFract β :=
  fun g ↦ ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩
instance : Coe (GenContFract α) (GenContFract β) :=
  ⟨coeFn⟩
@[simp, norm_cast]
theorem coe_toGenContFract {g : GenContFract α} :
    (g : GenContFract β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl
end coe
end GenContFract
def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1
variable (α)
def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }
variable {α}
namespace SimpContFract
variable [One α]
def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h ↦ by cases h⟩
instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩
instance : Coe (SimpContFract α) (GenContFract α) :=
  ⟨Subtype.val⟩
end SimpContFract
def SimpContFract.IsContFract [One α] [Zero α] [LT α]
    (s : SimpContFract α) : Prop :=
  ∀ (n : ℕ) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ → 0 < bₙ
variable (α)
def ContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsContFract }
variable {α}
namespace ContFract
variable [One α] [Zero α] [LT α]
def ofInteger (a : α) : ContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h ↦ by cases h⟩
instance : Inhabited (ContFract α) :=
  ⟨ofInteger 0⟩
instance : Coe (ContFract α) (SimpContFract α) :=
  ⟨Subtype.val⟩
instance : Coe (ContFract α) (GenContFract α) :=
  ⟨fun c ↦ c.val⟩
end ContFract
namespace GenContFract
variable {K : Type*} [DivisionRing K]
def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩
def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))
def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail
def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a
def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b
def convs (g : GenContFract K) : Stream' K :=
  fun n : ℕ ↦ g.nums n / g.dens n
def convs'Aux : Stream'.Seq (Pair K) → ℕ → K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convs'Aux s.tail n)
def convs' (g : GenContFract K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n
end GenContFract