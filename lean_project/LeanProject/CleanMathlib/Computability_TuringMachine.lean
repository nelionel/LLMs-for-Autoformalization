import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Vector.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.List.GetD
assert_not_exists MonoidWithZero
open Mathlib (Vector)
open Relation
open Nat (iterate)
open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)
namespace Turing
def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  ∃ n, l₂ = l₁ ++ List.replicate n default
@[refl]
theorem BlankExtends.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankExtends l l :=
  ⟨0, by simp⟩
@[trans]
theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankExtends l₁ l₂ → BlankExtends l₂ l₃ → BlankExtends l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩
theorem BlankExtends.below_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l l₁ → BlankExtends l l₂ → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length ≤ l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩
theorem BlankExtends.above_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l₁ l → BlankExtends l₂ l → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat.add_le_add_iff_right]
def BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁
@[refl]
theorem BlankRel.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankRel l l :=
  Or.inl (BlankExtends.refl _)
@[symm]
theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ → BlankRel l₂ l₁ :=
  Or.symm
@[trans]
theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankRel l₁ l₂ → BlankRel l₂ l₃ → BlankRel l₁ l₃ := by
  rintro (h₁ | h₁) (h₂ | h₂)
  · exact Or.inl (h₁.trans h₂)
  · rcases le_total l₁.length l₃.length with h | h
    · exact Or.inl (h₁.above_of_le h₂ h)
    · exact Or.inr (h₂.above_of_le h₁ h)
  · rcases le_total l₁.length l₃.length with h | h
    · exact Or.inl (h₁.below_of_le h₂ h)
    · exact Or.inr (h₂.below_of_le h₁ h)
  · exact Or.inr (h₂.trans h₁)
def BlankRel.above {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l₁ l ∧ BlankExtends l₂ l } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₂, Or.elim h id fun h' ↦ ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' ↦ ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)
def BlankRel.below {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l l₁ ∧ BlankExtends l l₂ } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' ↦ ?_⟩
    else ⟨l₂, Or.elim h (fun h' ↦ ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)
theorem BlankRel.equivalence (Γ) [Inhabited Γ] : Equivalence (@BlankRel Γ _) :=
  ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩
def BlankRel.setoid (Γ) [Inhabited Γ] : Setoid (List Γ) :=
  ⟨_, BlankRel.equivalence _⟩
def ListBlank (Γ) [Inhabited Γ] :=
  Quotient (BlankRel.setoid Γ)
instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩
instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩
protected abbrev ListBlank.liftOn {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ → α)
    (H : ∀ a b, BlankExtends a b → f a = f b) : α :=
  l.liftOn' f <| by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ → ListBlank Γ :=
  Quotient.mk''
@[elab_as_elim]
protected theorem ListBlank.induction_on {Γ} [Inhabited Γ] {p : ListBlank Γ → Prop}
    (q : ListBlank Γ) (h : ∀ a, p (ListBlank.mk a)) : p q :=
  Quotient.inductionOn' q h
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl
@[simp]
theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · cases' i with i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩
@[simp]
theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)
@[simp]
theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl
@[simp]
theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).head = a :=
  Quotient.ind' fun _ ↦ rfl
@[simp]
theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).tail = l :=
  Quotient.ind' fun _ ↦ rfl
@[simp]
theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] : ∀ l : ListBlank Γ, l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine fun l ↦ Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
    ∃ a l', l = ListBlank.cons a l' :=
  ⟨_, _, (ListBlank.cons_head_tail _).symm⟩
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) : Γ := by
  apply l.liftOn (fun l ↦ List.getI l n)
  rintro l _ ⟨i, rfl⟩
  cases' lt_or_le n _ with h h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_lt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂, List.getElem_append_right h, List.getElem_replicate]
@[simp]
theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (ListBlank.mk l).nth n = l.getI n :=
  rfl
@[simp]
theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl
@[simp]
theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
    l.nth (n + 1) = l.tail.nth n := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl
@[ext]
theorem ListBlank.ext {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
    (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ := by
  refine ListBlank.induction_on L₁ fun l₁ ↦ ListBlank.induction_on L₂ fun l₂ H ↦ ?_
  wlog h : l₁.length ≤ l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  refine List.ext_getElem ?_ fun i h h₂ ↦ Eq.symm ?_
  · simp only [Nat.add_sub_cancel' h, List.length_append, List.length_replicate]
  simp only [ListBlank.nth_mk] at H
  cases' lt_or_le i l₁.length with h' h'
  · simp [h', List.getElem_append _ h₂, ← List.getI_eq_getElem _ h, ← List.getI_eq_getElem _ h', H]
  · rw [List.getElem_append_right h', List.getElem_replicate,
      ← List.getI_eq_default _ h', H, List.getI_eq_getElem _ h]
@[simp]
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) : ℕ → ListBlank Γ → ListBlank Γ
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head
theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) (n i) (L : ListBlank Γ) :
    (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction' n with n IH generalizing i L
  · cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  · cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      simp only [ListBlank.nth_zero, ListBlank.head_cons, ListBlank.modifyNth]
    · simp only [IH, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.tail_cons, Nat.succ.injEq]
structure PointedMap.{u, v} (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] :
    Type max u v where
  f : Γ → Γ'
  map_pt' : f default = default
instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
  ⟨⟨default, rfl⟩⟩
instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') fun _ ↦ Γ → Γ' :=
  ⟨PointedMap.f⟩
theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ → Γ') (pt) :
    (PointedMap.mk f pt : Γ → Γ') = f :=
  rfl
@[simp]
theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    f default = default :=
  PointedMap.map_pt' _
@[simp]
theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ) :
    ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]
@[simp]
theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (ListBlank.mk l).map f = ListBlank.mk (l.map f) :=
  rfl
@[simp]
theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).head = f l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl
@[simp]
theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl
@[simp]
theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) := by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]
@[simp]
theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) := by
  refine l.inductionOn fun l ↦ ?_
  suffices ((mk l).map f).nth n = f ((mk l).nth n) by exact this
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp
def proj {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) :
    PointedMap (∀ i, Γ i) (Γ i) :=
  ⟨fun a ↦ a i, rfl⟩
theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) (L n) :
    (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
  rw [ListBlank.nth_map]; rfl
theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
    (f : Γ → Γ) (f' : Γ' → Γ') (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
    (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction' n with n IH generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]
@[simp]
def ListBlank.append {Γ} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)
@[simp]
theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]
theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine l₃.inductionOn fun l ↦ ?_
  suffices append (l₁ ++ l₂) (mk l) = append l₁ (append l₂ (mk l)) by exact this
  simp only [ListBlank.append_mk, List.append_assoc]
def ListBlank.flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ → List Γ')
    (hf : ∃ n, f default = List.replicate n default) : ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.flatMap l f))
  rintro l _ ⟨i, rfl⟩; cases' hf with n e; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append, mul_comm]; congr
  induction' i with i IH
  · rfl
  simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ,
    List.flatMap_cons]
@[deprecated (since := "2024-10-16")] alias ListBlank.bind := ListBlank.flatMap
@[simp]
theorem ListBlank.flatMap_mk
    {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ → List Γ') (hf) :
    (ListBlank.mk l).flatMap f hf = ListBlank.mk (l.flatMap f) :=
  rfl
@[deprecated (since := "2024-10-16")] alias ListBlank.bind_mk := ListBlank.flatMap_mk
@[simp]
theorem ListBlank.cons_flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
    (f : Γ → List Γ') (hf) : (l.cons a).flatMap f hf = (l.flatMap f hf).append (f a) := by
  refine l.inductionOn fun l ↦ ?_
  suffices ((mk l).cons a).flatMap f hf = ((mk l).flatMap f hf).append (f a) by exact this
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]
@[deprecated (since := "2024-10-16")] alias ListBlank.cons_bind := ListBlank.cons_flatMap
structure Tape (Γ : Type*) [Inhabited Γ] where
  head : Γ
  left : ListBlank Γ
  right : ListBlank Γ
instance Tape.inhabited {Γ} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨by constructor <;> apply default⟩
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited
def Tape.left₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.left.cons T.head
def Tape.right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.right.cons T.head
def Tape.move {Γ} [Inhabited Γ] : Dir → Tape Γ → Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩
@[simp]
theorem Tape.move_left_right {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.left).move Dir.right = T := by
  cases T; simp [Tape.move]
@[simp]
theorem Tape.move_right_left {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.right).move Dir.left = T := by
  cases T; simp [Tape.move]
def Tape.mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩
@[simp]
theorem Tape.mk'_left {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl
@[simp]
theorem Tape.mk'_head {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).head = R.head :=
  rfl
@[simp]
theorem Tape.mk'_right {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right = R.tail :=
  rfl
@[simp]
theorem Tape.mk'_right₀ {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right₀ = R :=
  ListBlank.cons_head_tail _
@[simp]
theorem Tape.mk'_left_right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : Tape.mk' T.left T.right₀ = T := by
  cases T
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, eq_self_iff_true,
    and_self_iff]
theorem Tape.exists_mk' {Γ} [Inhabited Γ] (T : Tape Γ) : ∃ L R, T = Tape.mk' L R :=
  ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩
@[simp]
theorem Tape.move_left_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, eq_self_iff_true, ListBlank.cons_head_tail,
    and_self_iff, ListBlank.tail_cons]
@[simp]
theorem Tape.move_right_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, eq_self_iff_true, ListBlank.cons_head_tail,
    and_self_iff, ListBlank.tail_cons]
def Tape.mk₂ {Γ} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)
def Tape.mk₁ {Γ} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l
def Tape.nth {Γ} [Inhabited Γ] (T : Tape Γ) : ℤ → Γ
  | 0 => T.head
  | (n + 1 : ℕ) => T.right.nth n
  | -(n + 1 : ℕ) => T.left.nth n
@[simp]
theorem Tape.nth_zero {Γ} [Inhabited Γ] (T : Tape Γ) : T.nth 0 = T.1 :=
  rfl
theorem Tape.right₀_nth {Γ} [Inhabited Γ] (T : Tape Γ) (n : ℕ) : T.right₀.nth n = T.nth n := by
  cases n <;> simp only [Tape.nth, Tape.right₀, Int.ofNat_zero, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]
@[simp]
theorem Tape.mk'_nth_nat {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : ℕ) :
    (Tape.mk' L R).nth n = R.nth n := by
  rw [← Tape.right₀_nth, Tape.mk'_right₀]
@[simp]
theorem Tape.move_left_nth {Γ} [Inhabited Γ] :
    ∀ (T : Tape Γ) (i : ℤ), (T.move Dir.left).nth i = T.nth (i - 1)
  | ⟨_, _, _⟩, -(_ + 1 : ℕ) => (ListBlank.nth_succ _ _).symm
  | ⟨_, _, _⟩, 0 => (ListBlank.nth_zero _).symm
  | ⟨_, _, _⟩, 1 => (ListBlank.nth_zero _).trans (ListBlank.head_cons _ _)
  | ⟨a, L, R⟩, (n + 1 : ℕ) + 1 => by
    rw [add_sub_cancel_right]
    change (R.cons a).nth (n + 1) = R.nth n
    rw [ListBlank.nth_succ, ListBlank.tail_cons]
@[simp]
theorem Tape.move_right_nth {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℤ) :
    (T.move Dir.right).nth i = T.nth (i + 1) := by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth, add_sub_cancel_right]
@[simp]
theorem Tape.move_right_n_head {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    ((Tape.move Dir.right)^[i] T).head = T.nth i := by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.ofNat_succ, iterate_succ, Function.comp_apply]
def Tape.write {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }
@[simp]
theorem Tape.write_self {Γ} [Inhabited Γ] : ∀ T : Tape Γ, T.write T.1 = T := by
  rintro ⟨⟩; rfl
@[simp]
theorem Tape.write_nth {Γ} [Inhabited Γ] (b : Γ) :
    ∀ (T : Tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
  | _, 0 => rfl
  | _, (_ + 1 : ℕ) => rfl
  | _, -(_ + 1 : ℕ) => rfl
@[simp]
theorem Tape.write_mk' {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (Tape.mk' L (R.cons a)).write b = Tape.mk' L (R.cons b) := by
  simp only [Tape.write, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, eq_self_iff_true,
    and_self_iff]
def Tape.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) : Tape Γ' :=
  ⟨f T.1, T.2.map f, T.3.map f⟩
@[simp]
theorem Tape.map_fst {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    ∀ T : Tape Γ, (T.map f).1 = f T.1 := by
  rintro ⟨⟩; rfl
@[simp]
theorem Tape.map_write {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ) :
    ∀ T : Tape Γ, (T.write b).map f = (T.map f).write (f b) := by
  rintro ⟨⟩; rfl
@[simp, nolint simpNF]
theorem Tape.write_move_right_n {Γ} [Inhabited Γ] (f : Γ → Γ) (L R : ListBlank Γ) (n : ℕ) :
    ((Tape.move Dir.right)^[n] (Tape.mk' L R)).write (f (R.nth n)) =
      (Tape.move Dir.right)^[n] (Tape.mk' L (R.modifyNth f n)) := by
  induction' n with n IH generalizing L R
  · simp only [ListBlank.nth_zero, ListBlank.modifyNth, iterate_zero_apply]
    rw [← Tape.write_mk', ListBlank.cons_head_tail]
  simp only [ListBlank.head_cons, ListBlank.nth_succ, ListBlank.modifyNth, Tape.move_right_mk',
    ListBlank.tail_cons, iterate_succ_apply, IH]
theorem Tape.map_move {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d) :
    (T.move d).map f = (T.map f).move d := by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map, eq_self_iff_true,
    ListBlank.map_cons, and_self_iff, ListBlank.tail_map]
theorem Tape.map_mk' {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ) :
    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f) := by
  simp only [Tape.mk', Tape.map, ListBlank.head_map, eq_self_iff_true, and_self_iff,
    ListBlank.tail_map]
theorem Tape.map_mk₂ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) := by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]
theorem Tape.map_mk₁ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (Tape.mk₁ l).map f = Tape.mk₁ (l.map f) :=
  Tape.map_mk₂ _ _ _
def eval {σ} (f : σ → Option σ) : σ → Part σ :=
  PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr
def Reaches {σ} (f : σ → Option σ) : σ → σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ f a
def Reaches₁ {σ} (f : σ → Option σ) : σ → σ → Prop :=
  TransGen fun a b ↦ b ∈ f a
theorem reaches₁_eq {σ} {f : σ → Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c :=
  TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm
theorem reaches_total {σ} {f : σ → Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b :=
  ReflTransGen.total_of_right_unique (fun _ _ _ ↦ Option.mem_unique) hab hac
theorem reaches₁_fwd {σ} {f : σ → Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b ∈ f a) :
    Reaches f b c := by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc
def Reaches₀ {σ} (f : σ → Option σ) (a b : σ) : Prop :=
  ∀ c, Reaches₁ f b c → Reaches₁ f a c
theorem Reaches₀.trans {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c
  | _, h₃ => h₁ _ (h₂ _ h₃)
@[refl]
theorem Reaches₀.refl {σ} {f : σ → Option σ} (a : σ) : Reaches₀ f a a
  | _, h => h
theorem Reaches₀.single {σ} {f : σ → Option σ} {a b : σ} (h : b ∈ f a) : Reaches₀ f a b
  | _, h₂ => h₂.head h
theorem Reaches₀.head {σ} {f : σ → Option σ} {a b c : σ} (h : b ∈ f a) (h₂ : Reaches₀ f b c) :
    Reaches₀ f a c :=
  (Reaches₀.single h).trans h₂
theorem Reaches₀.tail {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c ∈ f b) :
    Reaches₀ f a c :=
  h₁.trans (Reaches₀.single h)
theorem reaches₀_eq {σ} {f : σ → Option σ} {a b} (e : f a = f b) : Reaches₀ f a b
  | _, h => (reaches₁_eq e).2 h
theorem Reaches₁.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches₁ f a b) : Reaches₀ f a b
  | _, h₂ => h.trans h₂
theorem Reaches.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches f a b) : Reaches₀ f a b
  | _, h₂ => h₂.trans_right h
theorem Reaches₀.tail' {σ} {f : σ → Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c ∈ f b) :
    Reaches₁ f a c :=
  h _ (TransGen.single h₂)
@[elab_as_elim]
def evalInduction {σ} {f : σ → Option σ} {b : σ} {C : σ → Sort*} {a : σ}
    (h : b ∈ eval f a) (H : ∀ a, b ∈ eval f a → (∀ a', f a = some a' → C a') → C a) : C a :=
  PFun.fixInduction h fun a' ha' h' ↦
    H _ ha' fun b' e ↦ h' _ <| Part.mem_some_iff.2 <| by rw [e]; rfl
theorem mem_eval {σ} {f : σ → Option σ} {a b} : b ∈ eval f a ↔ Reaches f a b ∧ f b = none := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · 
    refine @evalInduction _ _ _ (fun a ↦ Reaches f a b ∧ f b = none) _ h fun a h IH ↦ ?_
    cases' e : f a with a'
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e]; rfl)]
      exact ⟨ReflTransGen.refl, e⟩
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
        cases Part.mem_some_iff.1 h
      cases' IH a' e with h₁ h₂
      exact ⟨ReflTransGen.head e h₁, h₂⟩
  · refine ReflTransGen.head_induction_on h₁ ?_ fun h _ IH ↦ ?_
    · refine PFun.mem_fix_iff.2 (Or.inl ?_)
      rw [h₂]
      apply Part.mem_some
    · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH⟩)
      rw [h]
      apply Part.mem_some
theorem eval_maximal₁ {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) (c) : ¬Reaches₁ f b c
  | bc => by
    let ⟨_, b0⟩ := mem_eval.1 h
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    cases b0.symm.trans h'
theorem eval_maximal {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) {c} : Reaches f b c ↔ c = b :=
  let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' ↦ by cases b0.symm.trans h'
theorem reaches_eval {σ} {f : σ → Option σ} {a b} (ab : Reaches f a b) : eval f a = eval f b := by
  refine Part.ext fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have ⟨ac, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb ↦ (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    exact mem_eval.2 ⟨ab.trans bc, c0⟩
def Respects {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂ → Prop) :=
  ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
    | some b₁ => ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)
theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂ := by
  induction' ab with c₁ ac c₁ d₁ _ cd IH
  · have := H aa
    rwa [show f₁ a₁ = _ from ac] at this
  · rcases IH with ⟨c₂, cc, ac₂⟩
    have := H cc
    rw [show f₁ c₁ = _ from cd] at this
    rcases this with ⟨d₂, dd, cd₂⟩
    exact ⟨_, dd, ac₂.trans cd₂⟩
theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  · exact ⟨_, aa, ReflTransGen.refl⟩
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    exact ⟨b₂, bb, h.to_reflTransGen⟩
theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) :
    ∃ c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by
  induction' ab with c₂ d₂ _ cd IH
  · exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
  · rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    · have := H ee
      revert this
      cases' eg : f₁ e₁ with g₁ <;> simp only [Respects, and_imp, exists_imp]
      · intro c0
        cases cd.symm.trans c0
      · intro g₂ gg cg
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        cases Option.mem_unique cd cd'
        exact ⟨_, _, dg, gg, ae.tail eg⟩
    · cases Option.mem_unique cd cd'
      exact ⟨_, _, de, ee, ae⟩
theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
    (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := by
  cases' mem_eval.1 ab with ab b0
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  refine ⟨_, bb, mem_eval.2 ⟨ab, ?_⟩⟩
  have := H bb; rwa [b0] at this
theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
    (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := by
  cases' mem_eval.1 ab with ab b0
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  refine ⟨_, cc, mem_eval.2 ⟨ac, ?_⟩⟩
  have := H cc
  cases' hfc : f₁ c₁ with d₁
  · rfl
  rw [hfc] at this
  rcases this with ⟨d₂, _, bd⟩
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  cases b0.symm.trans h
theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩
def FRespects {σ₁ σ₂} (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : Option σ₁ → Prop
  | some b₁ => Reaches₁ f₂ a₂ (tr b₁)
  | none => f₂ a₂ = none
theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂) :
    ∀ {b₁}, FRespects f₂ tr a₂ b₁ ↔ FRespects f₂ tr b₂ b₁
  | some _ => reaches₁_eq h
  | none => by unfold FRespects; rw [h]
theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
    (Respects f₁ f₂ fun a b ↦ tr a = b) ↔ ∀ ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁) :=
  forall_congr' fun a₁ ↦ by
    cases f₁ a₁ <;> simp only [FRespects, Respects, exists_eq_left', forall_eq']
theorem tr_eval' {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂)
    (H : Respects f₁ f₂ fun a b ↦ tr a = b) (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
  Part.ext fun b₂ ↦
    ⟨fun h ↦
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h ↦ by
      rcases (Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      rwa [bb] at h⟩
namespace TM0
section
variable (Γ : Type*)
variable (Λ : Type*)
inductive Stmt
  | move : Dir → Stmt
  | write : Γ → Stmt
local notation "Stmt₀" => Stmt Γ  
instance Stmt.inhabited [Inhabited Γ] : Inhabited Stmt₀ :=
  ⟨Stmt.write default⟩
@[nolint unusedArguments] 
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Λ × Stmt₀)
local notation "Machine₀" => Machine Γ Λ  
instance Machine.inhabited [Inhabited Λ] : Inhabited Machine₀ := by
  unfold Machine; infer_instance
structure Cfg [Inhabited Γ] where
  q : Λ
  Tape : Tape Γ
local notation "Cfg₀" => Cfg Γ Λ  
variable {Γ Λ}
variable [Inhabited Λ]
section
variable [Inhabited Γ]
instance Cfg.inhabited : Inhabited Cfg₀ := ⟨⟨default, default⟩⟩
def step (M : Machine₀) : Cfg₀ → Option Cfg₀ :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', match a with
    | Stmt.move d => T.move d
    | Stmt.write a => T.write a⟩
def Reaches (M : Machine₀) : Cfg₀ → Cfg₀ → Prop := ReflTransGen fun a b ↦ b ∈ step M a
def init (l : List Γ) : Cfg₀ := ⟨default, Tape.mk₁ l⟩
def eval (M : Machine₀) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀
def Supports (M : Machine₀) (S : Set Λ) :=
  default ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S
theorem step_supports (M : Machine₀) {S : Set Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₀}, c' ∈ step M c → c.q ∈ S → c'.q ∈ S := by
  intro ⟨q, T⟩ c' h₁ h₂
  rcases Option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩
  exact ss.2 h h₂
end
theorem univ_supports (M : Machine₀) : Supports M Set.univ := by
  constructor <;> intros <;> apply Set.mem_univ
end
section
variable {Γ : Type*} [Inhabited Γ]
variable {Γ' : Type*} [Inhabited Γ']
variable {Λ : Type*} [Inhabited Λ]
variable {Λ' : Type*} [Inhabited Λ']
def Stmt.map (f : PointedMap Γ Γ') : Stmt Γ → Stmt Γ'
  | Stmt.move d => Stmt.move d
  | Stmt.write a => Stmt.write (f a)
def Cfg.map (f : PointedMap Γ Γ') (g : Λ → Λ') : Cfg Γ Λ → Cfg Γ' Λ'
  | ⟨q, T⟩ => ⟨g q, T.map f⟩
variable (M : Machine Γ Λ) (f₁ : PointedMap Γ Γ') (f₂ : PointedMap Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)
def Machine.map : Machine Γ' Λ'
  | q, l => (M (g₂ q) (f₂ l)).map (Prod.map g₁ (Stmt.map f₁))
theorem Machine.map_step {S : Set Λ} (f₂₁ : Function.RightInverse f₁ f₂)
    (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    ∀ c : Cfg Γ Λ,
      c.q ∈ S → (step M c).map (Cfg.map f₁ g₁) = step (M.map f₁ f₂ g₁ g₂) (Cfg.map f₁ g₁ c)
  | ⟨q, T⟩, h => by
    unfold step Machine.map Cfg.map
    simp only [Turing.Tape.map_fst, g₂₁ q h, f₂₁ _]
    rcases M q T.1 with (_ | ⟨q', d | a⟩); · rfl
    · simp only [step, Cfg.map, Option.map_some', Tape.map_move f₁]
      rfl
    · simp only [step, Cfg.map, Option.map_some', Tape.map_write]
      rfl
theorem map_init (g₁ : PointedMap Λ Λ') (l : List Γ) : (init l).map f₁ g₁ = init (l.map f₁) :=
  congr (congr_arg Cfg.mk g₁.map_pt) (Tape.map_mk₁ _ _)
theorem Machine.map_respects (g₁ : PointedMap Λ Λ') (g₂ : Λ' → Λ) {S} (ss : Supports M S)
    (f₂₁ : Function.RightInverse f₁ f₂) (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    Respects (step M) (step (M.map f₁ f₂ g₁ g₂)) fun a b ↦ a.q ∈ S ∧ Cfg.map f₁ g₁ a = b := by
  intro c _ ⟨cs, rfl⟩
  cases e : step M c
  · rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e]
    rfl
  · refine ⟨_, ⟨step_supports M ss e cs, rfl⟩, TransGen.single ?_⟩
    rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e]
    rfl
end
end TM0
namespace TM1
section
variable (Γ : Type*)
variable (Λ : Type*)
variable (σ : Type*)
inductive Stmt
  | move : Dir → Stmt → Stmt
  | write : (Γ → σ → Γ) → Stmt → Stmt
  | load : (Γ → σ → σ) → Stmt → Stmt
  | branch : (Γ → σ → Bool) → Stmt → Stmt → Stmt
  | goto : (Γ → σ → Λ) → Stmt
  | halt : Stmt
local notation "Stmt₁" => Stmt Γ Λ σ  
open Stmt
instance Stmt.inhabited : Inhabited Stmt₁ := ⟨halt⟩
structure Cfg [Inhabited Γ] where
  l : Option Λ
  var : σ
  Tape : Tape Γ
local notation "Cfg₁" => Cfg Γ Λ σ  
instance Cfg.inhabited [Inhabited Γ] [Inhabited σ] : Inhabited Cfg₁ :=
  ⟨⟨default, default, default⟩⟩
variable {Γ Λ σ}
def stepAux [Inhabited Γ] : Stmt₁ → σ → Tape Γ → Cfg₁
  | move d q, v, T => stepAux q v (T.move d)
  | write a q, v, T => stepAux q v (T.write (a T.1 v))
  | load s q, v, T => stepAux q (s T.1 v) T
  | branch p q₁ q₂, v, T => cond (p T.1 v) (stepAux q₁ v T) (stepAux q₂ v T)
  | goto l, v, T => ⟨some (l T.1 v), v, T⟩
  | halt, v, T => ⟨none, v, T⟩
def step [Inhabited Γ] (M : Λ → Stmt₁) : Cfg₁ → Option Cfg₁
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, T⟩ => some (stepAux (M l) v T)
def SupportsStmt (S : Finset Λ) : Stmt₁ → Prop
  | move _ q => SupportsStmt S q
  | write _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ a v, l a v ∈ S
  | halt => True
open scoped Classical
noncomputable def stmts₁ : Stmt₁ → Finset Stmt₁
  | Q@(move _ q) => insert Q (stmts₁ q)
  | Q@(write _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q => {Q}
theorem stmts₁_self {q : Stmt₁} : q ∈ stmts₁ q := by
  cases q <;> simp only [stmts₁, Finset.mem_insert_self, Finset.mem_singleton_self]
theorem stmts₁_trans {q₁ q₂ : Stmt₁} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h₁₂)
  | branch p q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ <| IH₁ h₁₂)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ <| IH₂ h₁₂)
  | goto l => subst h₁₂; exact h₀₁
  | halt => subst h₁₂; exact h₀₁
  | _ _ q IH =>
    rcases h₁₂ with rfl | h₁₂
    · exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)
theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt₁} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch p q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | _ _ q IH => rcases h with (rfl | h) <;> [exact hs; exact IH h hs]
noncomputable def stmts (M : Λ → Stmt₁) (S : Finset Λ) : Finset (Option Stmt₁) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))
theorem stmts_trans {M : Λ → Stmt₁} {S : Finset Λ} {q₁ q₂ : Stmt₁} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩
variable [Inhabited Λ]
def Supports (M : Λ → Stmt₁) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)
theorem stmts_supportsStmt {M : Λ → Stmt₁} {S : Finset Λ} {q : Stmt₁} (ss : Supports M S) :
    some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)
variable [Inhabited Γ]
theorem step_supports (M : Λ → Stmt₁) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₁}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p T.1 v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | goto => exact Finset.some_mem_insertNone.2 (hs _ _)
    | halt => apply Multiset.mem_cons_self
    | _ _ q IH => exact IH _ _ hs
variable [Inhabited σ]
def init (l : List Γ) : Cfg₁ :=
  ⟨some default, default, Tape.mk₁ l⟩
def eval (M : Λ → Stmt₁) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀
end
end TM1
namespace TM1to0
variable {Γ : Type*}
variable {Λ : Type*} [Inhabited Λ]
variable {σ : Type*} [Inhabited σ]
local notation "Stmt₁" => TM1.Stmt Γ Λ σ
local notation "Cfg₁" => TM1.Cfg Γ Λ σ
local notation "Stmt₀" => TM0.Stmt Γ
variable (M : Λ → TM1.Stmt Γ Λ σ)  
set_option linter.unusedVariables false in
@[nolint unusedArguments] 
def Λ' (M : Λ → TM1.Stmt Γ Λ σ) :=
  Option Stmt₁ × σ
local notation "Λ'₁₀" => Λ' M 
instance : Inhabited Λ'₁₀ :=
  ⟨(some (M default), default)⟩
open TM0.Stmt
def trAux (s : Γ) : Stmt₁ → σ → Λ'₁₀ × Stmt₀
  | TM1.Stmt.move d q, v => ((some q, v), move d)
  | TM1.Stmt.write a q, v => ((some q, v), write (a s v))
  | TM1.Stmt.load a q, v => trAux s q (a s v)
  | TM1.Stmt.branch p q₁ q₂, v => cond (p s v) (trAux s q₁ v) (trAux s q₂ v)
  | TM1.Stmt.goto l, v => ((some (M (l s v)), v), write s)
  | TM1.Stmt.halt, v => ((none, v), write s)
local notation "Cfg₁₀" => TM0.Cfg Γ Λ'₁₀
def tr : TM0.Machine Γ Λ'₁₀
  | (none, _), _ => none
  | (some q, v), s => some (trAux M s q v)
def trCfg [Inhabited Γ] : Cfg₁ → Cfg₁₀
  | ⟨l, v, T⟩ => ⟨(l.map M, v), T⟩
theorem tr_respects [Inhabited Γ] :
    Respects (TM1.step M) (TM0.step (tr M)) fun (c₁ : Cfg₁) (c₂ : Cfg₁₀) ↦ trCfg M c₁ = c₂ :=
  fun_respects.2 fun ⟨l₁, v, T⟩ ↦ by
    cases' l₁ with l₁; · exact rfl
    simp only [trCfg, TM1.step, FRespects, Option.map]
    induction M l₁ generalizing v T with
    | move _ _ IH => exact TransGen.head rfl (IH _ _)
    | write _ _ IH => exact TransGen.head rfl (IH _ _)
    | load _ _ IH => exact (reaches₁_eq (by rfl)).2 (IH _ _)
    | branch p _ _ IH₁ IH₂ =>
      unfold TM1.stepAux; cases e : p T.1 v
      · exact (reaches₁_eq (by simp only [TM0.step, tr, trAux, e]; rfl)).2 (IH₂ _ _)
      · exact (reaches₁_eq (by simp only [TM0.step, tr, trAux, e]; rfl)).2 (IH₁ _ _)
    | _ =>
      exact TransGen.single (congr_arg some (congr (congr_arg TM0.Cfg.mk rfl) (Tape.write_self T)))
theorem tr_eval [Inhabited Γ] (l : List Γ) : TM0.eval (tr M) l = TM1.eval M l :=
  (congr_arg _ (tr_eval' _ _ _ (tr_respects M) ⟨some _, _, _⟩)).trans
    (by
      rw [Part.map_eq_map, Part.map_map, TM1.eval]
      congr with ⟨⟩)
variable [Fintype σ]
noncomputable def trStmts (S : Finset Λ) : Finset Λ'₁₀ :=
  (TM1.stmts M S) ×ˢ Finset.univ
open scoped Classical
attribute [local simp] TM1.stmts₁_self
theorem tr_supports {S : Finset Λ} (ss : TM1.Supports M S) :
    TM0.Supports (tr M) ↑(trStmts M S) := by
  constructor
  · apply Finset.mem_product.2
    constructor
    · simp only [default, TM1.stmts, Finset.mem_insertNone, Option.mem_def, Option.some_inj,
        forall_eq', Finset.mem_biUnion]
      exact ⟨_, ss.1, TM1.stmts₁_self⟩
    · apply Finset.mem_univ
  · intro q a q' s h₁ h₂
    rcases q with ⟨_ | q, v⟩; · cases h₁
    cases' q' with q' v'
    simp only [trStmts, Finset.mem_coe] at h₂ ⊢
    rw [Finset.mem_product] at h₂ ⊢
    simp only [Finset.mem_univ, and_true] at h₂ ⊢
    cases q'; · exact Multiset.mem_cons_self _ _
    simp only [tr, Option.mem_def] at h₁
    have := TM1.stmts_supportsStmt ss h₂
    revert this; induction q generalizing v with intro hs
    | move d q =>
      cases h₁; refine TM1.stmts_trans ?_ h₂
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    | write b q =>
      cases h₁; refine TM1.stmts_trans ?_ h₂
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    | load b q IH =>
      refine IH _ (TM1.stmts_trans ?_ h₂) h₁ hs
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    | branch p q₁ q₂ IH₁ IH₂ =>
      cases h : p a v <;> rw [trAux, h] at h₁
      · refine IH₂ _ (TM1.stmts_trans ?_ h₂) h₁ hs.2
        unfold TM1.stmts₁
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self)
      · refine IH₁ _ (TM1.stmts_trans ?_ h₂) h₁ hs.1
        unfold TM1.stmts₁
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self)
    | goto l =>
      cases h₁
      exact Finset.some_mem_insertNone.2 (Finset.mem_biUnion.2 ⟨_, hs _ _, TM1.stmts₁_self⟩)
    | halt => cases h₁
end TM1to0
namespace TM1to1
open TM1
variable {Γ : Type*}
theorem exists_enc_dec [Inhabited Γ] [Finite Γ] :
    ∃ (n : ℕ) (enc : Γ → Mathlib.Vector Bool n) (dec : Mathlib.Vector Bool n → Γ),
      enc default = Vector.replicate n false ∧ ∀ a, dec (enc a) = a := by
  rcases Finite.exists_equiv_fin Γ with ⟨n, ⟨e⟩⟩
  letI : DecidableEq Γ := e.decidableEq
  let G : Fin n ↪ Fin n → Bool :=
    ⟨fun a b ↦ a = b, fun a b h ↦
      Bool.of_decide_true <| (congr_fun h b).trans <| Bool.decide_true rfl⟩
  let H := (e.toEmbedding.trans G).trans (Equiv.vectorEquivFin _ _).symm.toEmbedding
  let enc := H.setValue default (Vector.replicate n false)
  exact ⟨_, enc, Function.invFun enc, H.setValue_eq _ _, Function.leftInverse_invFun enc.2⟩
variable {Λ σ : Type*}
local notation "Stmt₁" => Stmt Γ Λ σ
local notation "Cfg₁" => Cfg Γ Λ σ
inductive Λ'
  | normal : Λ → Λ'
  | write : Γ → Stmt₁ → Λ'
local notation "Λ'₁" => @Λ' Γ Λ σ  
instance [Inhabited Λ] : Inhabited Λ'₁ :=
  ⟨Λ'.normal default⟩
local notation "Stmt'₁" => Stmt Bool Λ'₁ σ
local notation "Cfg'₁" => Cfg Bool Λ'₁ σ
def readAux : ∀ n, (Mathlib.Vector Bool n → Stmt'₁) → Stmt'₁
  | 0, f => f Vector.nil
  | i + 1, f =>
    Stmt.branch (fun a _ ↦ a) (Stmt.move Dir.right <| readAux i fun v ↦ f (true ::ᵥ v))
      (Stmt.move Dir.right <| readAux i fun v ↦ f (false ::ᵥ v))
variable {n : ℕ} (enc : Γ → Mathlib.Vector Bool n) (dec : Mathlib.Vector Bool n → Γ)
def move (d : Dir) (q : Stmt'₁) : Stmt'₁ :=
  (Stmt.move d)^[n] q
local notation "moveₙ" => @move Γ Λ σ n  
def read (f : Γ → Stmt'₁) : Stmt'₁ :=
  readAux n fun v ↦ moveₙ Dir.left <| f (dec v)
def write : List Bool → Stmt'₁ → Stmt'₁
  | [], q => q
  | a :: l, q => (Stmt.write fun _ _ ↦ a) <| Stmt.move Dir.right <| write l q
def trNormal : Stmt₁ → Stmt'₁
  | Stmt.move d q => moveₙ d <| trNormal q
  | Stmt.write f q => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.write (f a s) q
  | Stmt.load f q => read dec fun a ↦ (Stmt.load fun _ s ↦ f a s) <| trNormal q
  | Stmt.branch p q₁ q₂ =>
    read dec fun a ↦ Stmt.branch (fun _ s ↦ p a s) (trNormal q₁) (trNormal q₂)
  | Stmt.goto l => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.normal (l a s)
  | Stmt.halt => Stmt.halt
theorem stepAux_move (d : Dir) (q : Stmt'₁) (v : σ) (T : Tape Bool) :
    stepAux (moveₙ d q) v T = stepAux q v ((Tape.move d)^[n] T) := by
  suffices ∀ i, stepAux ((Stmt.move d)^[i] q) v T = stepAux q v ((Tape.move d)^[i] T) from this n
  intro i; induction' i with i IH generalizing T; · rfl
  rw [iterate_succ', iterate_succ]
  simp only [stepAux, Function.comp_apply]
  rw [IH]
theorem supportsStmt_move {S : Finset Λ'₁} {d : Dir} {q : Stmt'₁} :
    SupportsStmt S (moveₙ d q) = SupportsStmt S q := by
  suffices ∀ {i}, SupportsStmt S ((Stmt.move d)^[i] q) = _ from this
  intro i; induction i generalizing q <;> simp only [*, iterate]; rfl
theorem supportsStmt_write {S : Finset Λ'₁} {l : List Bool} {q : Stmt'₁} :
    SupportsStmt S (write l q) = SupportsStmt S q := by
  induction' l with _ l IH <;> simp only [write, SupportsStmt, *]
theorem supportsStmt_read {S : Finset Λ'₁} :
    ∀ {f : Γ → Stmt'₁}, (∀ a, SupportsStmt S (f a)) → SupportsStmt S (read dec f) :=
  suffices
    ∀ (i) (f : Mathlib.Vector Bool i → Stmt'₁),
      (∀ v, SupportsStmt S (f v)) → SupportsStmt S (readAux i f)
    from fun hf ↦ this n _ (by intro; simp only [supportsStmt_move, hf])
  fun i f hf ↦ by
  induction' i with i IH; · exact hf _
  constructor <;> apply IH <;> intro <;> apply hf
variable (M : Λ → TM1.Stmt Γ Λ σ)  
section
variable [Inhabited Γ] (enc0 : enc default = Vector.replicate n false)
section
variable {enc}
def trTape' (L R : ListBlank Γ) : Tape Bool := by
  refine
      Tape.mk' (L.flatMap (fun x ↦ (enc x).toList.reverse) ⟨n, ?_⟩)
        (R.flatMap (fun x ↦ (enc x).toList) ⟨n, ?_⟩) <;>
    simp only [enc0, Vector.replicate, List.reverse_replicate, Bool.default_bool, Vector.toList_mk]
def trTape (T : Tape Γ) : Tape Bool :=
  trTape' enc0 T.left T.right₀
theorem trTape_mk' (L R : ListBlank Γ) : trTape enc0 (Tape.mk' L R) = trTape' enc0 L R := by
  simp only [trTape, Tape.mk'_left, Tape.mk'_right₀]
end
def tr : Λ'₁ → Stmt'₁
  | Λ'.normal l => trNormal dec (M l)
  | Λ'.write a q => write (enc a).toList <| moveₙ Dir.left <| trNormal dec q
def trCfg : Cfg₁ → Cfg'₁
  | ⟨l, v, T⟩ => ⟨l.map Λ'.normal, v, trTape enc0 T⟩
variable {enc}
theorem trTape'_move_left (L R : ListBlank Γ) :
    (Tape.move Dir.left)^[n] (trTape' enc0 L R) = trTape' enc0 L.tail (R.cons L.head) := by
  obtain ⟨a, L, rfl⟩ := L.exists_cons
  simp only [trTape', ListBlank.cons_flatMap, ListBlank.head_cons, ListBlank.tail_cons]
  suffices ∀ {L' R' l₁ l₂} (_ : Vector.toList (enc a) = List.reverseAux l₁ l₂),
      (Tape.move Dir.left)^[l₁.length]
      (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂ R')) =
      Tape.mk' L' (ListBlank.append (Vector.toList (enc a)) R') by
    simpa only [List.length_reverse, Vector.toList_length] using this (List.reverse_reverse _).symm
  intro _ _ l₁ l₂ e
  induction' l₁ with b l₁ IH generalizing l₂
  · cases e
    rfl
  simp only [List.length, List.cons_append, iterate_succ_apply]
  convert IH e
  simp only [ListBlank.tail_cons, ListBlank.append, Tape.move_left_mk', ListBlank.head_cons]
theorem trTape'_move_right (L R : ListBlank Γ) :
    (Tape.move Dir.right)^[n] (trTape' enc0 L R) = trTape' enc0 (L.cons R.head) R.tail := by
  suffices ∀ i L, (Tape.move Dir.right)^[i] ((Tape.move Dir.left)^[i] L) = L by
    refine (Eq.symm ?_).trans (this n _)
    simp only [trTape'_move_left, ListBlank.cons_head_tail, ListBlank.head_cons,
      ListBlank.tail_cons]
  intro i _
  induction' i with i IH
  · rfl
  rw [iterate_succ_apply, iterate_succ_apply', Tape.move_left_right, IH]
theorem stepAux_write (q : Stmt'₁) (v : σ) (a b : Γ) (L R : ListBlank Γ) :
    stepAux (write (enc a).toList q) v (trTape' enc0 L (ListBlank.cons b R)) =
      stepAux q v (trTape' enc0 (ListBlank.cons a L) R) := by
  simp only [trTape', ListBlank.cons_flatMap]
  suffices ∀ {L' R'} (l₁ l₂ l₂' : List Bool) (_ : l₂'.length = l₂.length),
      stepAux (write l₂ q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂' R')) =
      stepAux q v (Tape.mk' (L'.append (List.reverseAux l₂ l₁)) R') by
    exact this [] _ _ ((enc b).2.trans (enc a).2.symm)
  clear a b L R
  intro L' R' l₁ l₂ l₂' e
  induction' l₂ with a l₂ IH generalizing l₁ l₂'
  · cases List.length_eq_zero.1 e
    rfl
  cases' l₂' with b l₂' <;>
    simp only [List.length_nil, List.length_cons, Nat.succ_inj', reduceCtorEq] at e
  rw [List.reverseAux, ← IH (a :: l₁) l₂' e]
  simp only [stepAux, ListBlank.append, Tape.write_mk', Tape.move_right_mk', ListBlank.head_cons,
    ListBlank.tail_cons]
variable (encdec : ∀ a, dec (enc a) = a)
include encdec
theorem stepAux_read (f : Γ → Stmt'₁) (v : σ) (L R : ListBlank Γ) :
    stepAux (read dec f) v (trTape' enc0 L R) = stepAux (f R.head) v (trTape' enc0 L R) := by
  suffices ∀ f, stepAux (readAux n f) v (trTape' enc0 L R) =
      stepAux (f (enc R.head)) v (trTape' enc0 (L.cons R.head) R.tail) by
    rw [read, this, stepAux_move, encdec, trTape'_move_left enc0]
    simp only [ListBlank.head_cons, ListBlank.cons_head_tail, ListBlank.tail_cons]
  obtain ⟨a, R, rfl⟩ := R.exists_cons
  simp only [ListBlank.head_cons, ListBlank.tail_cons, trTape', ListBlank.cons_flatMap,
    ListBlank.append_assoc]
  suffices ∀ i f L' R' l₁ l₂ h,
      stepAux (readAux i f) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂ R')) =
      stepAux (f ⟨l₂, h⟩) v (Tape.mk' (ListBlank.append (l₂.reverseAux l₁) L') R') by
    intro f
    exact this n f (L.flatMap (fun x => (enc x).1.reverse) _)
      (R.flatMap (fun x => (enc x).1) _) [] _ (enc a).2
  clear f L a R
  intro i f L' R' l₁ l₂ _
  subst i
  induction' l₂ with a l₂ IH generalizing l₁
  · rfl
  trans
    stepAux (readAux l₂.length fun v ↦ f (a ::ᵥ v)) v
      (Tape.mk' ((L'.append l₁).cons a) (R'.append l₂))
  · dsimp [readAux, stepAux]
    simp only [ListBlank.head_cons, Tape.move_right_mk', ListBlank.tail_cons]
    cases a <;> rfl
  rw [← ListBlank.append, IH]
  rfl
variable {enc0} in
theorem tr_respects :
    Respects (step M) (step (tr enc dec M)) fun c₁ c₂ ↦ trCfg enc enc0 c₁ = c₂ :=
  fun_respects.2 fun ⟨l₁, v, T⟩ ↦ by
    obtain ⟨L, R, rfl⟩ := T.exists_mk'
    cases' l₁ with l₁
    · exact rfl
    suffices ∀ q R, Reaches (step (tr enc dec M)) (stepAux (trNormal dec q) v (trTape' enc0 L R))
        (trCfg enc enc0 (stepAux q v (Tape.mk' L R))) by
      refine TransGen.head' rfl ?_
      rw [trTape_mk']
      exact this _ R
    clear R l₁
    intro q R
    induction q generalizing v L R with
    | move d q IH =>
      cases d <;>
          simp only [trNormal, iterate, stepAux_move, stepAux, ListBlank.head_cons,
            Tape.move_left_mk', ListBlank.cons_head_tail, ListBlank.tail_cons,
            trTape'_move_left enc0, trTape'_move_right enc0] <;>
        apply IH
    | write f q IH =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux]
      refine ReflTransGen.head rfl ?_
      obtain ⟨a, R, rfl⟩ := R.exists_cons
      rw [tr, Tape.mk'_head, stepAux_write, ListBlank.head_cons, stepAux_move,
        trTape'_move_left enc0, ListBlank.head_cons, ListBlank.tail_cons, Tape.write_mk']
      apply IH
    | load a q IH =>
      simp only [trNormal, stepAux_read dec enc0 encdec]
      apply IH
    | branch p q₁ q₂ IH₁ IH₂ =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux, Tape.mk'_head]
      cases p R.head v <;> [apply IH₂; apply IH₁]
    | goto l =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux, trCfg, trTape_mk']
      apply ReflTransGen.refl
    | halt =>
      simp only [trNormal, stepAux, trCfg, stepAux_move, trTape'_move_left enc0,
        trTape'_move_right enc0, trTape_mk']
      apply ReflTransGen.refl
end
open scoped Classical
variable [Fintype Γ]
noncomputable def writes : Stmt₁ → Finset Λ'₁
  | Stmt.move _ q => writes q
  | Stmt.write _ q => (Finset.univ.image fun a ↦ Λ'.write a q) ∪ writes q
  | Stmt.load _ q => writes q
  | Stmt.branch _ q₁ q₂ => writes q₁ ∪ writes q₂
  | Stmt.goto _ => ∅
  | Stmt.halt => ∅
noncomputable def trSupp (S : Finset Λ) : Finset Λ'₁ :=
  S.biUnion fun l ↦ insert (Λ'.normal l) (writes (M l))
theorem tr_supports [Inhabited Λ] {S : Finset Λ} (ss : Supports M S) :
    Supports (tr enc dec M) (trSupp M S) :=
  ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert_self _ _⟩, fun q h ↦ by
    suffices ∀ q, SupportsStmt S q → (∀ q' ∈ writes q, q' ∈ trSupp M S) →
        SupportsStmt (trSupp M S) (trNormal dec q) ∧
        ∀ q' ∈ writes q, SupportsStmt (trSupp M S) (tr enc dec M q') by
      rcases Finset.mem_biUnion.1 h with ⟨l, hl, h⟩
      have :=
        this _ (ss.2 _ hl) fun q' hq ↦ Finset.mem_biUnion.2 ⟨_, hl, Finset.mem_insert_of_mem hq⟩
      rcases Finset.mem_insert.1 h with (rfl | h)
      exacts [this.1, this.2 _ h]
    intro q hs hw
    induction q with
    | move d q IH =>
      unfold writes at hw ⊢
      replace IH := IH hs hw; refine ⟨?_, IH.2⟩
      cases d <;> simp only [trNormal, iterate, supportsStmt_move, IH]
    | write f q IH =>
      unfold writes at hw ⊢
      simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, exists_prop, true_and]
        at hw ⊢
      replace IH := IH hs fun q hq ↦ hw q (Or.inr hq)
      refine ⟨supportsStmt_read _ fun a _ s ↦ hw _ (Or.inl ⟨_, rfl⟩), fun q' hq ↦ ?_⟩
      rcases hq with (⟨a, q₂, rfl⟩ | hq)
      · simp only [tr, supportsStmt_write, supportsStmt_move, IH.1]
      · exact IH.2 _ hq
    | load a q IH =>
      unfold writes at hw ⊢
      replace IH := IH hs hw
      exact ⟨supportsStmt_read _ fun _ ↦ IH.1, IH.2⟩
    | branch p q₁ q₂ IH₁ IH₂ =>
      unfold writes at hw ⊢
      simp only [Finset.mem_union] at hw ⊢
      replace IH₁ := IH₁ hs.1 fun q hq ↦ hw q (Or.inl hq)
      replace IH₂ := IH₂ hs.2 fun q hq ↦ hw q (Or.inr hq)
      exact ⟨supportsStmt_read _ fun _ ↦ ⟨IH₁.1, IH₂.1⟩, fun q ↦ Or.rec (IH₁.2 _) (IH₂.2 _)⟩
    | goto l =>
      simp only [writes, Finset.not_mem_empty]; refine ⟨?_, fun _ ↦ False.elim⟩
      refine supportsStmt_read _ fun a _ s ↦ ?_
      exact Finset.mem_biUnion.2 ⟨_, hs _ _, Finset.mem_insert_self _ _⟩
    | halt =>
      simp only [writes, Finset.not_mem_empty]; refine ⟨?_, fun _ ↦ False.elim⟩
      simp only [SupportsStmt, supportsStmt_move, trNormal]⟩
end TM1to1
namespace TM0to1
variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*} [Inhabited Λ]
inductive Λ'
  | normal : Λ → Λ'
  | act : TM0.Stmt Γ → Λ → Λ'
local notation "Λ'₁" => @Λ' Γ Λ  
instance : Inhabited Λ'₁ :=
  ⟨Λ'.normal default⟩
local notation "Cfg₀" => TM0.Cfg Γ Λ
local notation "Stmt₁" => TM1.Stmt Γ Λ'₁ Unit
local notation "Cfg₁" => TM1.Cfg Γ Λ'₁ Unit
variable (M : TM0.Machine Γ Λ)
open TM1.Stmt
def tr : Λ'₁ → Stmt₁
  | Λ'.normal q =>
    branch (fun a _ ↦ (M q a).isNone) halt <|
      goto fun a _ ↦ match M q a with
      | none => default 
      | some (q', s) => Λ'.act s q'
  | Λ'.act (TM0.Stmt.move d) q => move d <| goto fun _ _ ↦ Λ'.normal q
  | Λ'.act (TM0.Stmt.write a) q => (write fun _ _ ↦ a) <| goto fun _ _ ↦ Λ'.normal q
def trCfg : Cfg₀ → Cfg₁
  | ⟨q, T⟩ => ⟨cond (M q T.1).isSome (some (Λ'.normal q)) none, (), T⟩
theorem tr_respects : Respects (TM0.step M) (TM1.step (tr M)) fun a b ↦ trCfg M a = b :=
  fun_respects.2 fun ⟨q, T⟩ ↦ by
    cases' e : M q T.1 with val
    · simp only [TM0.step, trCfg, e]; exact Eq.refl none
    cases' val with q' s
    simp only [FRespects, TM0.step, trCfg, e, Option.isSome, cond, Option.map_some']
    revert e  
    have : TM1.step (tr M) ⟨some (Λ'.act s q'), (), T⟩ = some ⟨some (Λ'.normal q'), (), match s with
        | TM0.Stmt.move d => T.move d
        | TM0.Stmt.write a => T.write a⟩ := by
      cases' s with d a <;> rfl
    intro e
    refine TransGen.head ?_ (TransGen.head' this ?_)
    · simp only [TM1.step, TM1.stepAux]
      rw [e]
      rfl
    cases e' : M q' _
    · apply ReflTransGen.single
      simp only [TM1.step, TM1.stepAux]
      rw [e']
      rfl
    · rfl
end TM0to1
namespace TM2
variable {K : Type*}
variable (Γ : K → Type*)
variable (Λ : Type*)
variable (σ : Type*)
inductive Stmt
  | push : ∀ k, (σ → Γ k) → Stmt → Stmt
  | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | load : (σ → σ) → Stmt → Stmt
  | branch : (σ → Bool) → Stmt → Stmt → Stmt
  | goto : (σ → Λ) → Stmt
  | halt : Stmt
local notation "Stmt₂" => Stmt Γ Λ σ  
open Stmt
instance Stmt.inhabited : Inhabited Stmt₂ :=
  ⟨halt⟩
structure Cfg where
  l : Option Λ
  var : σ
  stk : ∀ k, List (Γ k)
local notation "Cfg₂" => Cfg Γ Λ σ  
instance Cfg.inhabited [Inhabited σ] : Inhabited Cfg₂ :=
  ⟨⟨default, default, default⟩⟩
variable {Γ Λ σ}
section
variable [DecidableEq K]
@[simp]
def stepAux : Stmt₂ → σ → (∀ k, List (Γ k)) → Cfg₂
  | push k f q, v, S => stepAux q v (update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch f q₁ q₂, v, S => cond (f v) (stepAux q₁ v S) (stepAux q₂ v S)
  | goto f, v, S => ⟨some (f v), v, S⟩
  | halt, v, S => ⟨none, v, S⟩
@[simp]
def step (M : Λ → Stmt₂) : Cfg₂ → Option Cfg₂
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)
def Reaches (M : Λ → Stmt₂) : Cfg₂ → Cfg₂ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a
end
def SupportsStmt (S : Finset Λ) : Stmt₂ → Prop
  | push _ _ q => SupportsStmt S q
  | peek _ _ q => SupportsStmt S q
  | pop _ _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ v, l v ∈ S
  | halt => True
section
open scoped Classical
noncomputable def stmts₁ : Stmt₂ → Finset Stmt₂
  | Q@(push _ _ q) => insert Q (stmts₁ q)
  | Q@(peek _ _ q) => insert Q (stmts₁ q)
  | Q@(pop _ _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q@(goto _) => {Q}
  | Q@halt => {Q}
theorem stmts₁_self {q : Stmt₂} : q ∈ stmts₁ q := by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]
theorem stmts₁_trans {q₁ q₂ : Stmt₂} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂)
  | branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IH₁ h₁₂))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (IH₂ h₁₂))
  | goto l => subst h₁₂; exact h₀₁
  | halt => subst h₁₂; exact h₀₁
  | load  _ q IH | _ _ _ q IH =>
    rcases h₁₂ with (rfl | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)
theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt₂} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ _ IH | _ _ _ _ IH => rcases h with (rfl | h) <;> [exact hs; exact IH h hs]
noncomputable def stmts (M : Λ → Stmt₂) (S : Finset Λ) : Finset (Option Stmt₂) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))
theorem stmts_trans {M : Λ → Stmt₂} {S : Finset Λ} {q₁ q₂ : Stmt₂} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩
end
variable [Inhabited Λ]
def Supports (M : Λ → Stmt₂) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)
theorem stmts_supportsStmt {M : Λ → Stmt₂} {S : Finset Λ} {q : Stmt₂} (ss : Supports M S) :
    some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)
variable [DecidableEq K]
theorem step_supports (M : Λ → Stmt₂) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₂}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | goto => exact Finset.some_mem_insertNone.2 (hs _)
    | halt => apply Multiset.mem_cons_self
    | load _ _ IH | _ _ _ _ IH => exact IH _ _ hs
variable [Inhabited σ]
def init (k : K) (L : List (Γ k)) : Cfg₂ :=
  ⟨some default, default, update (fun _ ↦ []) k L⟩
def eval (M : Λ → Stmt₂) (k : K) (L : List (Γ k)) : Part (List (Γ k)) :=
  (Turing.eval (step M) (init k L)).map fun c ↦ c.stk k
end TM2
namespace TM2to1
theorem stk_nth_val {K : Type*} {Γ : K → Type*} {L : ListBlank (∀ k, Option (Γ k))} {k S} (n)
    (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S).reverse) :
    L.nth n k = S.reverse[n]? := by
  rw [← proj_map_nth, hL, ← List.map_reverse, ListBlank.nth_mk,
    List.getI_eq_iget_getElem?, List.getElem?_map]
  cases S.reverse[n]? <;> rfl
variable {K : Type*}
variable {Γ : K → Type*}
variable {Λ σ : Type*}
local notation "Stmt₂" => TM2.Stmt Γ Λ σ
local notation "Cfg₂" => TM2.Cfg Γ Λ σ
def Γ' :=
  Bool × ∀ k, Option (Γ k)
local notation "Γ'₂₁" => @Γ' K Γ  
instance Γ'.inhabited : Inhabited Γ'₂₁ :=
  ⟨⟨false, fun _ ↦ none⟩⟩
instance Γ'.fintype [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] : Fintype Γ'₂₁ :=
  instFintypeProd _ _
def addBottom (L : ListBlank (∀ k, Option (Γ k))) : ListBlank Γ'₂₁ :=
  ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)
theorem addBottom_map (L : ListBlank (∀ k, Option (Γ k))) :
    (addBottom L).map ⟨Prod.snd, by rfl⟩ = L := by
  simp only [addBottom, ListBlank.map_cons]
  convert ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l ↦ ?_; simp
theorem addBottom_modifyNth (f : (∀ k, Option (Γ k)) → ∀ k, Option (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    (addBottom L).modifyNth (fun a ↦ (a.1, f a.2)) n = addBottom (L.modifyNth f n) := by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl
theorem addBottom_nth_snd (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth n).2 = L.nth n := by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]
theorem addBottom_nth_succ_fst (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth (n + 1)).1 = false := by
  rw [ListBlank.nth_succ, addBottom, ListBlank.tail_cons, ListBlank.nth_map]
theorem addBottom_head_fst (L : ListBlank (∀ k, Option (Γ k))) : (addBottom L).head.1 = true := by
  rw [addBottom, ListBlank.head_cons]
inductive StAct (k : K)
  | push : (σ → Γ k) → StAct k
  | peek : (σ → Option (Γ k) → σ) → StAct k
  | pop : (σ → Option (Γ k) → σ) → StAct k
local notation "StAct₂" => @StAct K Γ σ  
instance StAct.inhabited {k : K} : Inhabited (StAct₂ k) :=
  ⟨StAct.peek fun s _ ↦ s⟩
section
open StAct
def stRun {k : K} : StAct₂ k → Stmt₂ → Stmt₂
  | push f => TM2.Stmt.push k f
  | peek f => TM2.Stmt.peek k f
  | pop f => TM2.Stmt.pop k f
def stVar {k : K} (v : σ) (l : List (Γ k)) : StAct₂ k → σ
  | push _ => v
  | peek f => f v l.head?
  | pop f => f v l.head?
def stWrite {k : K} (v : σ) (l : List (Γ k)) : StAct₂ k → List (Γ k)
  | push f => f v :: l
  | peek _ => l
  | pop _ => l.tail
@[elab_as_elim]
def stmtStRec.{l} {C : Stmt₂ → Sort l} (H₁ : ∀ (k) (s : StAct₂ k) (q) (_ : C q), C (stRun s q))
    (H₂ : ∀ (a q) (_ : C q), C (TM2.Stmt.load a q))
    (H₃ : ∀ (p q₁ q₂) (_ : C q₁) (_ : C q₂), C (TM2.Stmt.branch p q₁ q₂))
    (H₄ : ∀ l, C (TM2.Stmt.goto l)) (H₅ : C TM2.Stmt.halt) : ∀ n, C n
  | TM2.Stmt.push _ f q => H₁ _ (push f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.peek _ f q => H₁ _ (peek f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.pop _ f q => H₁ _ (pop f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.load _ q => H₂ _ _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.branch _ q₁ q₂ => H₃ _ _ _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q₁) (stmtStRec H₁ H₂ H₃ H₄ H₅ q₂)
  | TM2.Stmt.goto _ => H₄ _
  | TM2.Stmt.halt => H₅
theorem supports_run (S : Finset Λ) {k : K} (s : StAct₂ k) (q : Stmt₂) :
    TM2.SupportsStmt S (stRun s q) ↔ TM2.SupportsStmt S q := by
  cases s <;> rfl
end
inductive Λ'
  | normal : Λ → Λ'
  | go (k : K) : StAct₂ k → Stmt₂ → Λ'
  | ret : Stmt₂ → Λ'
local notation "Λ'₂₁" => @Λ' K Γ Λ σ  
open Λ'
instance Λ'.inhabited [Inhabited Λ] : Inhabited Λ'₂₁ :=
  ⟨normal default⟩
local notation "Stmt₂₁" => TM1.Stmt Γ'₂₁ Λ'₂₁ σ
local notation "Cfg₂₁" => TM1.Cfg Γ'₂₁ Λ'₂₁ σ
open TM1.Stmt
section
variable [DecidableEq K]
def trStAct {k : K} (q : Stmt₂₁) : StAct₂ k → Stmt₂₁
  | StAct.push f => (write fun a s ↦ (a.1, update a.2 k <| some <| f s)) <| move Dir.right q
  | StAct.peek f => move Dir.left <| (load fun a s ↦ f s (a.2 k)) <| move Dir.right q
  | StAct.pop f =>
    branch (fun a _ ↦ a.1) (load (fun _ s ↦ f s none) q)
      (move Dir.left <|
        (load fun a s ↦ f s (a.2 k)) <| write (fun a _ ↦ (a.1, update a.2 k none)) q)
def trInit (k : K) (L : List (Γ k)) : List Γ'₂₁ :=
  let L' : List Γ'₂₁ := L.reverse.map fun a ↦ (false, update (fun _ ↦ none) k (some a))
  (true, L'.headI.2) :: L'.tail
theorem step_run {k : K} (q : Stmt₂) (v : σ) (S : ∀ k, List (Γ k)) : ∀ s : StAct₂ k,
    TM2.stepAux (stRun s q) v S = TM2.stepAux q (stVar v (S k) s) (update S k (stWrite v (S k) s))
  | StAct.push _ => rfl
  | StAct.peek f => by unfold stWrite; rw [Function.update_eq_self]; rfl
  | StAct.pop _ => rfl
end
def trNormal : Stmt₂ → Stmt₂₁
  | TM2.Stmt.push k f q => goto fun _ _ ↦ go k (StAct.push f) q
  | TM2.Stmt.peek k f q => goto fun _ _ ↦ go k (StAct.peek f) q
  | TM2.Stmt.pop k f q => goto fun _ _ ↦ go k (StAct.pop f) q
  | TM2.Stmt.load a q => load (fun _ ↦ a) (trNormal q)
  | TM2.Stmt.branch f q₁ q₂ => branch (fun _ ↦ f) (trNormal q₁) (trNormal q₂)
  | TM2.Stmt.goto l => goto fun _ s ↦ normal (l s)
  | TM2.Stmt.halt => halt
theorem trNormal_run {k : K} (s : StAct₂ k) (q : Stmt₂) :
    trNormal (stRun s q) = goto fun _ _ ↦ go k s q := by
  cases s <;> rfl
section
open scoped Classical
noncomputable def trStmts₁ : Stmt₂ → Finset Λ'₂₁
  | TM2.Stmt.push k f q => {go k (StAct.push f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.peek k f q => {go k (StAct.peek f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.pop k f q => {go k (StAct.pop f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.load _ q => trStmts₁ q
  | TM2.Stmt.branch _ q₁ q₂ => trStmts₁ q₁ ∪ trStmts₁ q₂
  | _ => ∅
theorem trStmts₁_run {k : K} {s : StAct₂ k} {q : Stmt₂} :
    trStmts₁ (stRun s q) = {go k s q, ret q} ∪ trStmts₁ q := by
  cases s <;> simp only [trStmts₁]
theorem tr_respects_aux₂ [DecidableEq K] {k : K} {q : Stmt₂₁} {v : σ} {S : ∀ k, List (Γ k)}
    {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) (o : StAct₂ k) :
    let v' := stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) =
          TM1.stepAux q v' ((Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))) := by
  simp only [Function.update_same]; cases o with simp only [stWrite, stVar, trStAct, TM1.stepAux]
  | push f =>
    have := Tape.write_move_right_n fun a : Γ' ↦ (a.1, update a.2 k (some (f v)))
    refine
      ⟨_, fun k' ↦ ?_, by
        erw [Tape.move_right_n_head, List.length, Tape.mk'_nth_nat, this,
          addBottom_modifyNth fun a ↦ update a k (some (f v)), Nat.add_one, iterate_succ']
        rfl⟩
    refine ListBlank.ext fun i ↦ ?_
    rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
    by_cases h' : k' = k
    · subst k'
      split_ifs with h
        <;> simp only [List.reverse_cons, Function.update_same, ListBlank.nth_mk, List.map]
      · rw [List.getI_eq_getElem _, List.getElem_append_right] <;>
        simp only [List.length_append, List.length_reverse, List.length_map, ← h,
          Nat.sub_self, List.length_singleton, List.getElem_singleton,
          le_refl, Nat.lt_succ_self]
      rw [← proj_map_nth, hL, ListBlank.nth_mk]
      cases' lt_or_gt_of_ne h with h h
      · rw [List.getI_append]
        simpa only [List.length_map, List.length_reverse] using h
      · rw [gt_iff_lt] at h
        rw [List.getI_eq_default, List.getI_eq_default] <;>
          simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
            List.length_append, List.length_map]
    · split_ifs <;> rw [Function.update_noteq h', ← proj_map_nth, hL]
      rw [Function.update_noteq h']
  | peek f =>
    rw [Function.update_eq_self]
    use L, hL; rw [Tape.move_left_right]; congr
    cases e : S k; · rfl
    rw [List.length_cons, iterate_succ', Function.comp, Tape.move_right_left,
      Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ (hL k), e,
      List.reverse_cons, ← List.length_reverse, List.getElem?_concat_length]
    rfl
  | pop f =>
    cases' e : S k with hd tl
    · simp only [Tape.mk'_head, ListBlank.head_cons, Tape.move_left_mk', List.length,
        Tape.write_mk', List.head?, iterate_zero_apply, List.tail_nil]
      rw [← e, Function.update_eq_self]
      exact ⟨L, hL, by rw [addBottom_head_fst, cond]⟩
    · refine
        ⟨_, fun k' ↦ ?_, by
          erw [List.length_cons, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst,
            cond_false, iterate_succ', Function.comp, Tape.move_right_left, Tape.move_right_n_head,
            Tape.mk'_nth_nat, Tape.write_move_right_n fun a : Γ' ↦ (a.1, update a.2 k none),
            addBottom_modifyNth fun a ↦ update a k none, addBottom_nth_snd,
            stk_nth_val _ (hL k), e,
            show (List.cons hd tl).reverse[tl.length]? = some hd by
              rw [List.reverse_cons, ← List.length_reverse, List.getElem?_concat_length],
            List.head?, List.tail]⟩
      refine ListBlank.ext fun i ↦ ?_
      rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
      by_cases h' : k' = k
      · subst k'
        split_ifs with h <;> simp only [Function.update_same, ListBlank.nth_mk, List.tail]
        · rw [List.getI_eq_default]
          · rfl
          rw [h, List.length_reverse, List.length_map]
        rw [← proj_map_nth, hL, ListBlank.nth_mk, e, List.map, List.reverse_cons]
        cases' lt_or_gt_of_ne h with h h
        · rw [List.getI_append]
          simpa only [List.length_map, List.length_reverse] using h
        · rw [gt_iff_lt] at h
          rw [List.getI_eq_default, List.getI_eq_default] <;>
            simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
              List.length_append, List.length_map]
      · split_ifs <;> rw [Function.update_noteq h', ← proj_map_nth, hL]
        rw [Function.update_noteq h']
end
variable [DecidableEq K]
variable (M : Λ → TM2.Stmt Γ Λ σ)  
def tr : Λ'₂₁ → Stmt₂₁
  | normal q => trNormal (M q)
  | go k s q =>
    branch (fun a _ ↦ (a.2 k).isNone) (trStAct (goto fun _ _ ↦ ret q) s)
      (move Dir.right <| goto fun _ _ ↦ go k s q)
  | ret q => branch (fun a _ ↦ a.1) (trNormal q) (move Dir.left <| goto fun _ _ ↦ ret q)
inductive TrCfg : Cfg₂ → Cfg₂₁ → Prop
  | mk {q : Option Λ} {v : σ} {S : ∀ k, List (Γ k)} (L : ListBlank (∀ k, Option (Γ k))) :
    (∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) →
      TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩
theorem tr_respects_aux₁ {k} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n ≤ S.length) :
    Reaches₀ (TM1.step (tr M)) ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction' n with n IH; · rfl
  apply (IH (le_of_lt H)).tail
  rw [iterate_succ_apply']
  simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
    addBottom_nth_snd, Option.mem_def]
  rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
  · rfl
  · rwa [List.length_reverse]
theorem tr_respects_aux₃ {q v} {L : ListBlank (∀ k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M))
    ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
    ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction' n with n IH; · rfl
  refine Reaches₀.head ?_ IH
  simp only [Option.mem_def, TM1.step]
  rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
    addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
  rfl
theorem tr_respects_aux {q v T k} {S : ∀ k, List (Γ k)}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct₂ k)
    (IH : ∀ {v : σ} {S : ∀ k : K, List (Γ k)} {T : ListBlank (∀ k, Option (Γ k))},
      (∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) →
      ∃ b, TrCfg (TM2.stepAux q v S) b ∧
        Reaches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) :
    ∃ b, TrCfg (TM2.stepAux (stRun o q) v S) b ∧ Reaches (TM1.step (tr M))
      (TM1.stepAux (trNormal (stRun o q)) v (Tape.mk' ∅ (addBottom T))) b := by
  simp only [trNormal_run, step_run]
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) hT o
  have := hgo.tail' rfl
  rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
    stk_nth_val _ (hT k), List.getElem?_eq_none (le_of_eq (List.length_reverse _)),
    Option.isNone, cond, hrun, TM1.stepAux] at this
  obtain ⟨c, gc, rc⟩ := IH hT'
  refine ⟨c, gc, (this.to₀.trans (tr_respects_aux₃ M _) c (TransGen.head' rfl ?_)).to_reflTransGen⟩
  rw [tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
  exact rc
attribute [local simp] Respects TM2.step TM2.stepAux trNormal
theorem tr_respects : Respects (TM2.step M) (TM1.step (tr M)) TrCfg := by
  intro c₁ c₂ h
  cases' h with l v S L hT
  cases' l with l; · constructor
  rsuffices ⟨b, c, r⟩ : ∃ b, _ ∧ Reaches (TM1.step (tr M)) _ _
  · exact ⟨b, c, TransGen.head' rfl r⟩
  simp only [tr]
  generalize M l = N
  induction N using stmtStRec generalizing v S L hT with
  | H₁ k s q IH => exact tr_respects_aux M hT s @IH
  | H₂ a _ IH => exact IH _ hT
  | H₃ p q₁ q₂ IH₁ IH₂ =>
    unfold TM2.stepAux trNormal TM1.stepAux
    beta_reduce
    cases p v <;> [exact IH₂ _ hT; exact IH₁ _ hT]
  | H₄ => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩
  | H₅ => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩
section
variable [Inhabited Λ] [Inhabited σ]
theorem trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.init k L) (TM1.init (trInit k L) : Cfg₂₁) := by
  rw [(_ : TM1.init _ = _)]
  · refine ⟨ListBlank.mk (L.reverse.map fun a ↦ update default k (some a)), fun k' ↦ ?_⟩
    refine ListBlank.ext fun i ↦ ?_
    rw [ListBlank.map_mk, ListBlank.nth_mk, List.getI_eq_iget_getElem?, List.map_map]
    have : ((proj k').f ∘ fun a => update (β := fun k => Option (Γ k)) default k (some a))
      = fun a => (proj k').f (update (β := fun k => Option (Γ k)) default k (some a)) := rfl
    rw [this, List.getElem?_map, proj, PointedMap.mk_val]
    simp only []
    by_cases h : k' = k
    · subst k'
      simp only [Function.update_same]
      rw [ListBlank.nth_mk, List.getI_eq_iget_getElem?, ← List.map_reverse, List.getElem?_map]
    · simp only [Function.update_noteq h]
      rw [ListBlank.nth_mk, List.getI_eq_iget_getElem?, List.map, List.reverse_nil]
      cases L.reverse[i]? <;> rfl
  · rw [trInit, TM1.init]
    congr <;> cases L.reverse <;> try rfl
    simp only [List.map_map, List.tail_cons, List.map]
    rfl
theorem tr_eval_dom (k) (L : List (Γ k)) :
    (TM1.eval (tr M) (trInit k L)).Dom ↔ (TM2.eval M k L).Dom :=
  Turing.tr_eval_dom (tr_respects M) (trCfg_init k L)
theorem tr_eval (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ ∈ TM1.eval (tr M) (trInit k L))
    (H₂ : L₂ ∈ TM2.eval M k L) :
    ∃ (S : ∀ k, List (Γ k)) (L' : ListBlank (∀ k, Option (Γ k))),
      addBottom L' = L₁ ∧
        (∀ k, L'.map (proj k) = ListBlank.mk ((S k).map some).reverse) ∧ S k = L₂ := by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := Turing.tr_eval (tr_respects M) (trCfg_init k L) h₂
  cases Part.mem_unique h₁ h₃
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩
end
section
open scoped Classical
variable [Inhabited Λ]
noncomputable def trSupp (S : Finset Λ) : Finset Λ'₂₁ :=
  S.biUnion fun l ↦ insert (normal l) (trStmts₁ (M l))
theorem tr_supports {S} (ss : TM2.Supports M S) : TM1.Supports (tr M) (trSupp M S) :=
  ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 <| Or.inl rfl⟩, fun l' h ↦ by
    suffices ∀ (q) (_ : TM2.SupportsStmt S q) (_ : ∀ x ∈ trStmts₁ q, x ∈ trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        ∀ l' ∈ trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M l') by
      rcases Finset.mem_biUnion.1 h with ⟨l, lS, h⟩
      have :=
        this _ (ss.2 l lS) fun x hx ↦ Finset.mem_biUnion.2 ⟨_, lS, Finset.mem_insert_of_mem hx⟩
      rcases Finset.mem_insert.1 h with (rfl | h) <;> [exact this.1; exact this.2 _ h]
    clear h l'
    refine stmtStRec ?_ ?_ ?_ ?_ ?_
    · intro _ s _ IH ss' sub 
      rw [TM2to1.supports_run] at ss'
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at sub
      have hgo := sub _ (Or.inl <| Or.inl rfl)
      have hret := sub _ (Or.inl <| Or.inr rfl)
      cases' IH ss' fun x hx ↦ sub x <| Or.inr hx with IH₁ IH₂
      refine ⟨by simp only [trNormal_run, TM1.SupportsStmt]; intros; exact hgo, fun l h ↦ ?_⟩
      rw [trStmts₁_run] at h
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at h
      rcases h with (⟨rfl | rfl⟩ | h)
      · cases s
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
        · exact ⟨⟨fun _ _ ↦ hret, fun _ _ ↦ hret⟩, fun _ _ ↦ hgo⟩
      · unfold TM1.SupportsStmt TM2to1.tr
        exact ⟨IH₁, fun _ _ ↦ hret⟩
      · exact IH₂ _ h
    · intro _ _ IH ss' sub 
      unfold TM2to1.trStmts₁ at sub ⊢
      exact IH ss' sub
    · intro _ _ _ IH₁ IH₂ ss' sub 
      unfold TM2to1.trStmts₁ at sub
      cases' IH₁ ss'.1 fun x hx ↦ sub x <| Finset.mem_union_left _ hx with IH₁₁ IH₁₂
      cases' IH₂ ss'.2 fun x hx ↦ sub x <| Finset.mem_union_right _ hx with IH₂₁ IH₂₂
      refine ⟨⟨IH₁₁, IH₂₁⟩, fun l h ↦ ?_⟩
      rw [trStmts₁] at h
      rcases Finset.mem_union.1 h with (h | h) <;> [exact IH₁₂ _ h; exact IH₂₂ _ h]
    · intro _ ss' _ 
      simp only [trStmts₁, Finset.not_mem_empty]; refine ⟨?_, fun _ ↦ False.elim⟩
      exact fun _ v ↦ Finset.mem_biUnion.2 ⟨_, ss' v, Finset.mem_insert_self _ _⟩
    · intro _ _ 
      simp only [trStmts₁, Finset.not_mem_empty]
      exact ⟨trivial, fun _ ↦ False.elim⟩⟩
end
end TM2to1
end Turing
set_option linter.style.longFile 2700