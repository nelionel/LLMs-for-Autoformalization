import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Pi
universe u v
open Finset
class FinEnum (α : Sort*) where
  card : ℕ
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]
attribute [instance 100] FinEnum.decEq
namespace FinEnum
variable {α : Type u} {β : α → Type v}
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β where
  card := card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq
def ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) :
    FinEnum α where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.indexOf x, by rw [List.indexOf_lt_length]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [List.indexOf_getElem h']⟩
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map (equiv).symm
open Function
@[simp]
theorem mem_toList [FinEnum α] (x : α) : x ∈ toList α := by
  simp [toList]; exists equiv x; simp
@[simp]
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simpa using h _)
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])
instance _root_.ULift.instFinEnum [FinEnum α] : FinEnum (ULift α) :=
  ⟨card α, Equiv.ulift.trans equiv⟩
@[simp]
theorem card_ulift [FinEnum (ULift α)] [FinEnum α] : card (ULift α) = card α :=
  Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift |>.trans equiv⟩
section ULift
variable [FinEnum α] (a : α) (a' : ULift α) (i : Fin (card α))
@[simp] lemma equiv_up : equiv (ULift.up a) = equiv a := rfl
@[simp] lemma equiv_down : equiv a'.down = equiv a' := rfl
@[simp] lemma up_equiv_symm : ULift.up (equiv.symm i) = (equiv (α := ULift α)).symm i := rfl
@[simp] lemma down_equiv_symm : ((equiv (α := ULift α)).symm i).down = equiv.symm i := rfl
end ULift
instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x
instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x
instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by cases x; simp
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp
instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp
instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)
@[simp]
theorem card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n := Fin.equiv_iff_eq.mp ⟨equiv.symm⟩
instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩
def Finset.enum [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← Finset.enum xs
    [r, insert x r]
@[simp]
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s ∈ Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs := by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_not_mem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_iff_not_imp_left] at hs
      simp +contextual [eq_comm (a := s), or_iff_not_imp_left, hs]
instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by intro; simp)
instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)
instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).flatMap fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)
instance PSigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)
instance PSigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ'a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim
instance PSigma.finEnumPropRight {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
instance PSigma.finEnumPropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    FinEnum (Σ'a, β a) :=
  if h : ∃ a, β a then ofList [⟨h.fst, h.snd⟩] (by rintro ⟨⟩; simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim
instance [DecidableEq α] (xs : List α) : FinEnum { x : α // x ∈ xs } := ofList xs.attach (by simp)
instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map (equiv).symm.toEmbedding
  complete := by intros; simp
theorem card_eq_fintypeCard {α : Type u} [FinEnum α] [Fintype α] : card α = Fintype.card α :=
  Fintype.truncEquivFin α |>.inductionOn (fun h ↦ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩)
theorem card_unique {α : Type u} (e₁ e₂ : FinEnum α) : e₁.card = e₂.card :=
  calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
  _ = _ := @card_eq_fintypeCard _ e₂ inferInstance |>.symm
theorem card_eq_zero_iff {α : Type u} [FinEnum α] : card α = 0 ↔ IsEmpty α :=
  Eq.congr_left card_eq_fintypeCard |>.trans Fintype.card_eq_zero_iff
theorem card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.mpr ‹_›
theorem card_pos_iff {α : Type u} [FinEnum α] : 0 < card α ↔ Nonempty α :=
  card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff
lemma card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < card α :=
  card_pos_iff.mpr ‹_›
lemma card_ne_zero {α : Type*} [FinEnum α] [Nonempty α] : card α ≠ 0 := card_pos.ne'
theorem card_eq_one (α : Type u) [FinEnum α] [Unique α] : card α = 1 :=
  card_eq_fintypeCard.trans <| Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩
instance [IsEmpty α] : Unique (FinEnum α) where
  default := ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    show FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x
def ofIsEmpty [IsEmpty α] : FinEnum α := default
instance [Unique α] : Unique (FinEnum α) where
  default := ⟨1, Equiv.equivOfUnique α (Fin 1)⟩
  uniq e := by
    show FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_one α
    · funext x y
      cases decEq x y <;> cases decidableEq_of_subsingleton x y <;>
      first | rfl | contradiction
def ofUnique [Unique α] : FinEnum α := default
end FinEnum
namespace List
variable {α : Type*} [FinEnum α] {β : α → Type*} [∀ a, FinEnum (β a)]
open FinEnum
theorem mem_pi_toList (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) :=
  (mem_pi _ _).mpr fun _ _ ↦ mem_toList _
def Pi.enum (β : α → Type*) [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))
theorem Pi.mem_enum (f : ∀ a, β a) :
    f ∈ Pi.enum β := by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩
instance Pi.finEnum : FinEnum (∀ a, β a) :=
  ofList (Pi.enum _) fun _ => Pi.mem_enum _
instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by intro; simp; ext hp'; cases hp hp')
end List