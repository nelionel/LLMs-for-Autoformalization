import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.PNat.Equiv
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Directed
import Mathlib.Order.RelIso.Basic
open Option List Nat Function
class Encodable (α : Type*) where
  encode : α → ℕ
  decode : ℕ → Option α
  encodek : ∀ a, decode (encode a) = some a
attribute [simp] Encodable.encodek
namespace Encodable
variable {α : Type*} {β : Type*}
universe u
theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e => Option.some.inj <| by rw [← encodek, e, encodek]
@[simp]
theorem encode_inj [Encodable α] {a b : α} : encode a = encode b ↔ a = b :=
  encode_injective.eq_iff
instance (priority := 400) countable [Encodable α] : Countable α where
  exists_injective_nat' := ⟨_,encode_injective⟩
theorem surjective_decode_iget (α : Type*) [Encodable α] [Inhabited α] :
    Surjective fun n => ((Encodable.decode n).iget : α) := fun x =>
  ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩
def decidableEqOfEncodable (α) [Encodable α] : DecidableEq α
  | _, _ => decidable_of_iff _ encode_inj
def ofLeftInjection [Encodable α] (f : β → α) (finv : α → Option β)
    (linv : ∀ b, finv (f b) = some b) : Encodable β :=
  ⟨fun b => encode (f b), fun n => (decode n).bind finv, fun b => by
    simp [Encodable.encodek, linv]⟩
def ofLeftInverse [Encodable α] (f : β → α) (finv : α → β) (linv : ∀ b, finv (f b) = b) :
    Encodable β :=
  ofLeftInjection f (some ∘ finv) fun b => congr_arg some (linv b)
def ofEquiv (α) [Encodable α] (e : β ≃ α) : Encodable β :=
  ofLeftInverse e e.symm e.left_inv
theorem encode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (b : β) :
    @encode _ (ofEquiv _ e) b = encode (e b) :=
  rfl
theorem decode_ofEquiv {α β} [Encodable α] (e : β ≃ α) (n : ℕ) :
    @decode _ (ofEquiv _ e) n = (decode n).map e.symm :=
  show Option.bind _ _ = Option.map _ _
  by rw [Option.map_eq_bind]
instance _root_.Nat.encodable : Encodable ℕ :=
  ⟨id, some, fun _ => rfl⟩
@[simp]
theorem encode_nat (n : ℕ) : encode n = n :=
  rfl
@[simp 1100]
theorem decode_nat (n : ℕ) : decode n = some n :=
  rfl
instance (priority := 100) _root_.IsEmpty.toEncodable [IsEmpty α] : Encodable α :=
  ⟨isEmptyElim, fun _ => none, isEmptyElim⟩
instance _root_.PUnit.encodable : Encodable PUnit :=
  ⟨fun _ => 0, fun n => Nat.casesOn n (some PUnit.unit) fun _ => none, fun _ => by simp⟩
@[simp]
theorem encode_star : encode PUnit.unit = 0 :=
  rfl
@[simp]
theorem decode_unit_zero : decode 0 = some PUnit.unit :=
  rfl
@[simp]
theorem decode_unit_succ (n) : decode (succ n) = (none : Option PUnit) :=
  rfl
instance _root_.Option.encodable {α : Type*} [h : Encodable α] : Encodable (Option α) :=
  ⟨fun o => Option.casesOn o Nat.zero fun a => succ (encode a), fun n =>
    Nat.casesOn n (some none) fun m => (decode m).map some, fun o => by
    cases o <;> dsimp; simp [encodek, Nat.succ_ne_zero]⟩
@[simp]
theorem encode_none [Encodable α] : encode (@none α) = 0 :=
  rfl
@[simp]
theorem encode_some [Encodable α] (a : α) : encode (some a) = succ (encode a) :=
  rfl
@[simp]
theorem decode_option_zero [Encodable α] : (decode 0 : Option (Option α))= some none :=
  rfl
@[simp]
theorem decode_option_succ [Encodable α] (n) :
    (decode (succ n) : Option (Option α)) = (decode n).map some :=
  rfl
def decode₂ (α) [Encodable α] (n : ℕ) : Option α :=
  (decode n).bind (Option.guard fun a => encode a = n)
theorem mem_decode₂' [Encodable α] {n : ℕ} {a : α} :
    a ∈ decode₂ α n ↔ a ∈ decode n ∧ encode a = n := by
  simpa [decode₂, bind_eq_some] using
    ⟨fun ⟨_, h₁, rfl, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨_, h₁, rfl, h₂⟩⟩
theorem mem_decode₂ [Encodable α] {n : ℕ} {a : α} : a ∈ decode₂ α n ↔ encode a = n :=
  mem_decode₂'.trans (and_iff_right_of_imp fun e => e ▸ encodek _)
theorem decode₂_eq_some [Encodable α] {n : ℕ} {a : α} : decode₂ α n = some a ↔ encode a = n :=
  mem_decode₂
@[simp]
theorem decode₂_encode [Encodable α] (a : α) : decode₂ α (encode a) = some a := by
  ext
  simp [mem_decode₂, eq_comm, decode₂_eq_some]
theorem decode₂_ne_none_iff [Encodable α] {n : ℕ} :
    decode₂ α n ≠ none ↔ n ∈ Set.range (encode : α → ℕ) := by
  simp_rw [Set.range, Set.mem_setOf_eq, Ne, Option.eq_none_iff_forall_not_mem,
    Encodable.mem_decode₂, not_forall, not_not]
theorem decode₂_is_partial_inv [Encodable α] : IsPartialInv encode (decode₂ α) := fun _ _ =>
  mem_decode₂
theorem decode₂_inj [Encodable α] {n : ℕ} {a₁ a₂ : α} (h₁ : a₁ ∈ decode₂ α n)
    (h₂ : a₂ ∈ decode₂ α n) : a₁ = a₂ :=
  encode_injective <| (mem_decode₂.1 h₁).trans (mem_decode₂.1 h₂).symm
theorem encodek₂ [Encodable α] (a : α) : decode₂ α (encode a) = some a :=
  mem_decode₂.2 rfl
def decidableRangeEncode (α : Type*) [Encodable α] : DecidablePred (· ∈ Set.range (@encode α _)) :=
  fun x =>
  decidable_of_iff (Option.isSome (decode₂ α x))
    ⟨fun h => ⟨Option.get _ h, by rw [← decode₂_is_partial_inv (Option.get _ h), Option.some_get]⟩,
      fun ⟨n, hn⟩ => by rw [← hn, encodek₂]; exact rfl⟩
def equivRangeEncode (α : Type*) [Encodable α] : α ≃ Set.range (@encode α _) where
  toFun := fun a : α => ⟨encode a, Set.mem_range_self _⟩
  invFun n :=
    Option.get _
      (show isSome (decode₂ α n.1) by cases' n.2 with x hx; rw [← hx, encodek₂]; exact rfl)
  left_inv a := by dsimp; rw [← Option.some_inj, Option.some_get, encodek₂]
  right_inv := fun ⟨n, x, hx⟩ => by
    apply Subtype.eq
    dsimp
    conv =>
      rhs
      rw [← hx]
    rw [encode_injective.eq_iff, ← Option.some_inj, Option.some_get, ← hx, encodek₂]
def _root_.Unique.encodable [Unique α] : Encodable α :=
  ⟨fun _ => 0, fun _ => some default, Unique.forall_iff.2 rfl⟩
section Sum
variable [Encodable α] [Encodable β]
def encodeSum : α ⊕ β → ℕ
  | Sum.inl a => 2 * encode a
  | Sum.inr b => 2 * encode b + 1
def decodeSum (n : ℕ) : Option (α ⊕ β) :=
  match boddDiv2 n with
  | (false, m) => (decode m : Option α).map Sum.inl
  | (_, m) => (decode m : Option β).map Sum.inr
instance _root_.Sum.encodable : Encodable (α ⊕ β) :=
  ⟨encodeSum, decodeSum, fun s => by cases s <;> simp [encodeSum, div2_val, decodeSum, encodek]⟩
@[simp]
theorem encode_inl (a : α) : @encode (α ⊕ β) _ (Sum.inl a) = 2 * (encode a) :=
  rfl
@[simp]
theorem encode_inr (b : β) : @encode (α ⊕ β) _ (Sum.inr b) = 2 * (encode b) + 1 :=
  rfl
@[simp]
theorem decode_sum_val (n : ℕ) : (decode n : Option (α ⊕ β)) = decodeSum n :=
  rfl
end Sum
instance _root_.Bool.encodable : Encodable Bool :=
  ofEquiv (Unit ⊕ Unit) Equiv.boolEquivPUnitSumPUnit
@[simp]
theorem encode_true : encode true = 1 :=
  rfl
@[simp]
theorem encode_false : encode false = 0 :=
  rfl
@[simp]
theorem decode_zero : (decode 0 : Option Bool) = some false :=
  rfl
@[simp]
theorem decode_one : (decode 1 : Option Bool) = some true :=
  rfl
theorem decode_ge_two (n) (h : 2 ≤ n) : (decode n : Option Bool) = none := by
  suffices decodeSum n = none by
    change (decodeSum n).bind _ = none
    rw [this]
    rfl
  have : 1 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le]
    exacts [h, by decide]
  cases' exists_eq_succ_of_ne_zero (_root_.ne_of_gt this) with m e
  simp only [decodeSum, boddDiv2_eq, div2_val]; cases bodd n <;> simp [e]
noncomputable instance _root_.Prop.encodable : Encodable Prop :=
  ofEquiv Bool Equiv.propEquivBool
section Sigma
variable {γ : α → Type*} [Encodable α] [∀ a, Encodable (γ a)]
def encodeSigma : Sigma γ → ℕ
  | ⟨a, b⟩ => pair (encode a) (encode b)
def decodeSigma (n : ℕ) : Option (Sigma γ) :=
  let (n₁, n₂) := unpair n
  (decode n₁).bind fun a => (decode n₂).map <| Sigma.mk a
instance _root_.Sigma.encodable : Encodable (Sigma γ) :=
  ⟨encodeSigma, decodeSigma, fun ⟨a, b⟩ => by
    simp [encodeSigma, decodeSigma, unpair_pair, encodek]⟩
@[simp]
theorem decode_sigma_val (n : ℕ) :
    (decode n : Option (Sigma γ)) =
      (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Sigma.mk a :=
  rfl
@[simp]
theorem encode_sigma_val (a b) : @encode (Sigma γ) _ ⟨a, b⟩ = pair (encode a) (encode b) :=
  rfl
end Sigma
section Prod
variable [Encodable α] [Encodable β]
instance Prod.encodable : Encodable (α × β) :=
  ofEquiv _ (Equiv.sigmaEquivProd α β).symm
@[simp]
theorem decode_prod_val (n : ℕ) :
    (@decode (α × β) _ n : Option (α × β))
      = (decode n.unpair.1).bind fun a => (decode n.unpair.2).map <| Prod.mk a := by
  simp only [decode_ofEquiv, Equiv.symm_symm, decode_sigma_val]
  cases (decode n.unpair.1 : Option α) <;> cases (decode n.unpair.2 : Option β)
  <;> rfl
@[simp]
theorem encode_prod_val (a b) : @encode (α × β) _ (a, b) = pair (encode a) (encode b) :=
  rfl
end Prod
section Subtype
open Subtype Decidable
variable {P : α → Prop} [encA : Encodable α] [decP : DecidablePred P]
def encodeSubtype : { a : α // P a } → ℕ
  | ⟨v,_⟩ => encode v
def decodeSubtype (v : ℕ) : Option { a : α // P a } :=
  (decode v).bind fun a => if h : P a then some ⟨a, h⟩ else none
instance _root_.Subtype.encodable : Encodable { a : α // P a } :=
  ⟨encodeSubtype, decodeSubtype, fun ⟨v, h⟩ => by simp [encodeSubtype, decodeSubtype, encodek, h]⟩
theorem Subtype.encode_eq (a : Subtype P) : encode a = encode a.val := by cases a; rfl
end Subtype
instance _root_.Fin.encodable (n) : Encodable (Fin n) :=
  ofEquiv _ Fin.equivSubtype
instance _root_.Int.encodable : Encodable ℤ :=
  ofEquiv _ Equiv.intEquivNat
instance _root_.PNat.encodable : Encodable ℕ+ :=
  ofEquiv _ Equiv.pnatEquivNat
instance _root_.ULift.encodable [Encodable α] : Encodable (ULift α) :=
  ofEquiv _ Equiv.ulift
instance _root_.PLift.encodable [Encodable α] : Encodable (PLift α) :=
  ofEquiv _ Equiv.plift
noncomputable def ofInj [Encodable β] (f : α → β) (hf : Injective f) : Encodable α :=
  ofLeftInjection f (partialInv f) fun _ => (partialInv_of_injective hf _ _).2 rfl
noncomputable def ofCountable (α : Type*) [Countable α] : Encodable α :=
  Nonempty.some <|
    let ⟨f, hf⟩ := exists_injective_nat α
    ⟨ofInj f hf⟩
@[simp]
theorem nonempty_encodable : Nonempty (Encodable α) ↔ Countable α :=
  ⟨fun ⟨h⟩ => @Encodable.countable α h, fun h => ⟨@ofCountable _ h⟩⟩
end Encodable
theorem nonempty_encodable (α : Type*) [Countable α] : Nonempty (Encodable α) :=
  ⟨Encodable.ofCountable _⟩
instance : Countable ℕ+ := by delta PNat; infer_instance
section ULower
attribute [local instance] Encodable.decidableRangeEncode
def ULower (α : Type*) [Encodable α] : Type :=
  Set.range (Encodable.encode : α → ℕ)
instance {α : Type*} [Encodable α] : DecidableEq (ULower α) := by
  delta ULower; exact Encodable.decidableEqOfEncodable _
instance {α : Type*} [Encodable α] : Encodable (ULower α) := by
  delta ULower; infer_instance
end ULower
namespace ULower
variable (α : Type*) [Encodable α]
def equiv : α ≃ ULower α :=
  Encodable.equivRangeEncode α
variable {α}
def down (a : α) : ULower α :=
  equiv α a
instance [Inhabited α] : Inhabited (ULower α) :=
  ⟨down default⟩
def up (a : ULower α) : α :=
  (equiv α).symm a
@[simp]
theorem down_up {a : ULower α} : down a.up = a :=
  Equiv.right_inv _ _
@[simp]
theorem up_down {a : α} : (down a).up = a := by
  simp [up, down,Equiv.left_inv _ _, Equiv.symm_apply_apply]
@[simp]
theorem up_eq_up {a b : ULower α} : a.up = b.up ↔ a = b :=
  Equiv.apply_eq_iff_eq _
@[simp]
theorem down_eq_down {a b : α} : down a = down b ↔ a = b :=
  Equiv.apply_eq_iff_eq _
@[ext]
protected theorem ext {a b : ULower α} : a.up = b.up → a = b :=
  up_eq_up.1
end ULower
namespace Encodable
section FindA
variable {α : Type*} (p : α → Prop) [Encodable α] [DecidablePred p]
private def good : Option α → Prop
  | some a => p a
  | none => False
private def decidable_good : DecidablePred (good p) :=
  fun n => by
    cases n <;> unfold good <;> dsimp <;> infer_instance
attribute [local instance] decidable_good
open Encodable
variable {p}
def chooseX (h : ∃ x, p x) : { a : α // p a } :=
  have : ∃ n, good p (decode n) :=
    let ⟨w, pw⟩ := h
    ⟨encode w, by simp [good, encodek, pw]⟩
  match (motive := ∀ o, good p o → { a // p a }) _, Nat.find_spec this with
  | some a, h => ⟨a, h⟩
def choose (h : ∃ x, p x) : α :=
  (chooseX h).1
theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (chooseX h).2
end FindA
theorem axiom_of_choice {α : Type*} {β : α → Type*} {R : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (R x y)] (H : ∀ x, ∃ y, R x y) : ∃ f : ∀ a, β a, ∀ x, R x (f x) :=
  ⟨fun x => choose (H x), fun x => choose_spec (H x)⟩
theorem skolem {α : Type*} {β : α → Type*} {P : ∀ x, β x → Prop} [∀ a, Encodable (β a)]
    [∀ x y, Decidable (P x y)] : (∀ x, ∃ y, P x y) ↔ ∃ f : ∀ a, β a, ∀ x, P x (f x) :=
  ⟨axiom_of_choice, fun ⟨_, H⟩ x => ⟨_, H x⟩⟩
def encode' (α) [Encodable α] : α ↪ ℕ :=
  ⟨Encodable.encode, Encodable.encode_injective⟩
instance {α} [Encodable α] : IsAntisymm _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).isAntisymm
instance {α} [Encodable α] : IsTotal _ (Encodable.encode' α ⁻¹'o (· ≤ ·)) :=
  (RelEmbedding.preimage _ _).isTotal
end Encodable
namespace Directed
open Encodable
variable {α : Type*} {β : Type*} [Encodable α] [Inhabited α]
protected noncomputable def sequence {r : β → β → Prop} (f : α → β) (hf : Directed r f) : ℕ → α
  | 0 => default
  | n + 1 =>
    let p := Directed.sequence f hf n
    match (decode n : Option α) with
    | none => Classical.choose (hf p p)
    | some a => Classical.choose (hf p a)
theorem sequence_mono_nat {r : β → β → Prop} {f : α → β} (hf : Directed r f) (n : ℕ) :
    r (f (hf.sequence f n)) (f (hf.sequence f (n + 1))) := by
  dsimp [Directed.sequence]
  generalize hf.sequence f n = p
  cases' (decode n : Option α) with a
  · exact (Classical.choose_spec (hf p p)).1
  · exact (Classical.choose_spec (hf p a)).1
theorem rel_sequence {r : β → β → Prop} {f : α → β} (hf : Directed r f) (a : α) :
    r (f a) (f (hf.sequence f (encode a + 1))) := by
  simp only [Directed.sequence, add_eq, add_zero, encodek, and_self]
  exact (Classical.choose_spec (hf _ a)).2
variable [Preorder β] {f : α → β}
section
variable (hf : Directed (· ≤ ·) f)
theorem sequence_mono : Monotone (f ∘ hf.sequence f) :=
  monotone_nat_of_le_succ <| hf.sequence_mono_nat
theorem le_sequence (a : α) : f a ≤ f (hf.sequence f (encode a + 1)) :=
  hf.rel_sequence a
end
section
variable (hf : Directed (· ≥ ·) f)
theorem sequence_anti : Antitone (f ∘ hf.sequence f) :=
  antitone_nat_of_succ_le <| hf.sequence_mono_nat
theorem sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) ≤ f a :=
  hf.rel_sequence a
end
end Directed
section Quotient
open Encodable Quotient
variable {α : Type*} {s : Setoid α} [@DecidableRel α (· ≈ ·)] [Encodable α]
def Quotient.rep (q : Quotient s) : α :=
  choose (exists_rep q)
theorem Quotient.rep_spec (q : Quotient s) : ⟦q.rep⟧ = q :=
  choose_spec (exists_rep q)
def encodableQuotient : Encodable (Quotient s) :=
  ⟨fun q => encode q.rep, fun n => Quotient.mk'' <$> decode n, by
    rintro ⟨l⟩; dsimp; rw [encodek]; exact congr_arg some ⟦l⟧.rep_spec⟩
end Quotient