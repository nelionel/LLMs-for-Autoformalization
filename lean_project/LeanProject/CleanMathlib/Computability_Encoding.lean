import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Option.Basic
import Mathlib.SetTheory.Cardinal.Basic
universe u v
open Cardinal
namespace Computability
structure Encoding (α : Type u) where
  Γ : Type v
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ x, decode (encode x) = some x
theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  ΓFin : Fintype Γ
instance Γ.fintype {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq
instance Γ'.fintype : Fintype Γ' :=
  ⟨⟨{.blank, .bit true, .bit false, .bra, .ket, .comma}, by decide⟩,
    by intro; cases_type* Γ' Bool <;> decide⟩
instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default
theorem leftInverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' :=
  fun x => Bool.casesOn x rfl rfl
theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective (Exists.intro sectionΓ'Bool leftInverse_section_inclusion)
def encodePosNum : PosNum → List Bool
  | PosNum.one    => [true]
  | PosNum.bit0 n => false :: encodePosNum n
  | PosNum.bit1 n => true :: encodePosNum n
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n
def decodePosNum : List Bool → PosNum
  | false :: l => PosNum.bit0 (decodePosNum l)
  | true  :: l => ite (l = []) PosNum.one (PosNum.bit1 (decodePosNum l))
  | _          => PosNum.one
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l
def decodeNat : List Bool → Nat := fun l => decodeNum l
theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun _m => List.cons_ne_nil _ _) fun _m =>
    List.cons_ne_nil _ _
theorem decode_encodePosNum : ∀ n, decodePosNum (encodePosNum n) = n := by
  intro n
  induction' n with m hm m hm <;> unfold encodePosNum decodePosNum
  · rfl
  · rw [hm]
    exact if_neg (encodePosNum_nonempty m)
  · exact congr_arg PosNum.bit0 hm
theorem decode_encodeNum : ∀ n, decodeNum (encodeNum n) = n := by
  intro n
  cases' n with n <;> unfold encodeNum decodeNum
  · rfl
  rw [decode_encodePosNum n]
  rw [PosNum.cast_to_num]
  exact if_neg (encodePosNum_nonempty n)
theorem decode_encodeNat : ∀ n, decodeNat (encodeNat n) = n := by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg ((↑) : Num → ℕ) (decode_encodeNum n)
def encodingNatBool : Encoding ℕ where
  Γ := Bool
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)
def finEncodingNatBool : FinEncoding ℕ :=
  ⟨encodingNatBool, Bool.fintype⟩
def encodingNatΓ' : Encoding ℕ where
  Γ := Γ'
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x :=
    congr_arg _ <| by
      rw [List.map_map, leftInverse_section_inclusion.id, List.map_id, decode_encodeNat]
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', Γ'.fintype⟩
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true :: unaryEncodeNat n
def unaryDecodeNat : List Bool → Nat :=
  List.length
theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (_m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n
def unaryFinEncodingNat : FinEncoding ℕ where
  Γ := Bool
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype
def encodeBool : Bool → List Bool := pure
def decodeBool : List Bool → Bool
  | b :: _ => b
  | _ => Inhabited.default
theorem decode_encodeBool (b : Bool) : decodeBool (encodeBool b) = b := rfl
def finEncodingBoolBool : FinEncoding Bool where
  Γ := Bool
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype
instance inhabitedFinEncoding : Inhabited (FinEncoding Bool) :=
  ⟨finEncodingBoolBool⟩
instance inhabitedEncoding : Inhabited (Encoding Bool) :=
  ⟨finEncodingBoolBool.toEncoding⟩
theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩
theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Countable e.Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0
theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : #α ≤ ℵ₀ :=
  e.toEncoding.card_le_aleph0
end Computability