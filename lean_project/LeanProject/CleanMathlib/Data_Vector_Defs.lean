import Mathlib.Data.List.Defs
import Mathlib.Tactic.Common
assert_not_exists Monoid
namespace Mathlib
universe u v w
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
namespace Vector
variable {α β σ φ : Type*} {n : ℕ} {p : α → Prop}
instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩
@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩
@[reducible, nolint unusedArguments]
def length (_ : Vector α n) : ℕ :=
  n
open Nat
def head : Vector α (Nat.succ n) → α
  | ⟨a :: _, _⟩ => a
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩
theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl
@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨_ :: _, _⟩ => rfl
def toList (v : Vector α n) : List α :=
  v.1
def get (l : Vector α n) (i : Fin n) : α :=
  l.1.get <| i.cast l.2.symm
def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u}
    (H : ∀ l : List α, C ⟨l, rfl⟩) {n : ℕ} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩
@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
@[simp]
theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl
def pmap (f : (a : α) → p a → β) :
    (v : Vector α n) → (∀ x ∈ v.toList, p x) → Vector β n
  | ⟨l, h⟩, hp => ⟨List.pmap f l hp, by simp [h]⟩
@[simp]
theorem pmap_nil (f : (a : α) → p a → β) (hp : ∀ x ∈ nil.toList, p x) :
    nil.pmap f hp = nil := rfl
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate n a⟩
def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩
def eraseIdx (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.eraseIdx l i.1, by rw [l.length_eraseIdx_of_lt] <;> rw [p]; exact i.2⟩
@[deprecated (since := "2024-05-04")] alias removeNth := eraseIdx
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i ↦ f i.succ)
protected def congr {n m : ℕ} (h : n = m) : Vector α n → Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩
section Accum
open Prod
def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩
def mapAccumr₂ (f : α → β → σ → σ × φ) : Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩
end Accum
section Shift
def shiftLeftFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by simp) <|
    append (drop i v) (replicate (min n i) fill)
def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by omega) <| append (replicate (min n i) fill) (take (n - i) v)
end Shift
protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)
@[simp]
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl
@[simp]
theorem toList_nil : toList nil = @List.nil α :=
  rfl
@[simp]
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2
@[simp]
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v; rfl
@[simp]
theorem toList_append {n m : ℕ} (v : Vector α n) (w : Vector α m) :
    toList (append v w) = toList v ++ toList w := by
  cases v
  cases w
  rfl
@[simp]
theorem toList_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl
@[simp]
theorem toList_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl
instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩
lemma getElem_def (v : Vector α n) (i : ℕ) {hi : i < n} :
    v[i] = v.toList[i]'(by simpa) := rfl
lemma toList_getElem (v : Vector α n) (i : ℕ) {hi : i < v.toList.length} :
    v.toList[i] = v[i]'(by simp_all) := rfl
end Vector
end Mathlib