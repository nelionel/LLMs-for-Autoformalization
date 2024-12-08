import Mathlib.Algebra.Group.Defs
import Batteries.Data.List.Basic
variable {α β δ : Type*} [AddZeroClass δ] [Min δ]
namespace Levenshtein
structure Cost (α β δ : Type*) where
  delete : α → δ
  insert : β → δ
  substitute : α → β → δ
@[simps]
def defaultCost [DecidableEq α] : Cost α α ℕ where
  delete _ := 1
  insert _ := 1
  substitute a b := if a = b then 0 else 1
instance [DecidableEq α] : Inhabited (Cost α α ℕ) := ⟨defaultCost⟩
@[simps]
def weightCost (f : α → ℕ) : Cost α α ℕ where
  delete a := f a
  insert b := f b
  substitute a b := max (f a) (f b)
@[simps!]
def stringLengthCost : Cost String String ℕ := weightCost String.length
@[simps!]
def stringLogLengthCost : Cost String String ℕ := weightCost fun s => Nat.log2 (s.length + 1)
variable (C : Cost α β δ)
def impl
    (xs : List α) (y : β) (d : {r : List δ // 0 < r.length}) : {r : List δ // 0 < r.length} :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[C.insert y + ds.getLast (List.length_pos.mp w)], by simp⟩)
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
      ⟨min (C.delete x + r[0]) (min (C.insert y + d₀) (C.substitute x y + d₁)) :: r, by simp⟩)
variable {C}
variable (x : α) (xs : List α) (y : β) (d : δ) (ds : List δ) (w : 0 < (d :: ds).length)
theorem impl_cons (w' : 0 < List.length ds) :
    impl C (x :: xs) y ⟨d :: ds, w⟩ =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      ⟨min (C.delete x + r[0]) (min (C.insert y + d) (C.substitute x y + ds[0])) :: r, by simp⟩ :=
  match ds, w' with | _ :: _, _ => rfl
theorem impl_cons_fst_zero (h : 0 < (impl C (x :: xs) y ⟨d :: ds, w⟩).val.length)
    (w' : 0 < List.length ds) : (impl C (x :: xs) y ⟨d :: ds, w⟩).1[0] =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      min (C.delete x + r[0]) (min (C.insert y + d) (C.substitute x y + ds[0])) :=
  match ds, w' with | _ :: _, _ => rfl
theorem impl_length (d : {r : List δ // 0 < r.length}) (w : d.1.length = xs.length + 1) :
    (impl C xs y d).1.length = xs.length + 1 := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
    dsimp [impl]
    match d, w with
    | ⟨d₁ :: d₂ :: ds, _⟩, w =>
      dsimp
      congr 1
      exact ih ⟨d₂ :: ds, (by simp)⟩ (by simpa using w)
end Levenshtein
open Levenshtein
variable (C : Cost α β δ)
def suffixLevenshtein (xs : List α) (ys : List β) : {r : List δ // 0 < r.length} :=
  ys.foldr
    (impl C xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(C.delete a + r[0]) :: r, by simp⟩))
variable {C}
theorem suffixLevenshtein_length (xs : List α) (ys : List β) :
    (suffixLevenshtein C xs ys).1.length = xs.length + 1 := by
  induction ys with
  | nil =>
    dsimp [suffixLevenshtein]
    induction xs with
    | nil => rfl
    | cons _ xs ih =>
      simp_all
  | cons y ys ih =>
    dsimp [suffixLevenshtein]
    rw [impl_length]
    exact ih
theorem suffixLevenshtein_eq (xs : List α) (y ys) :
    impl C xs y (suffixLevenshtein C xs ys) = suffixLevenshtein C xs (y :: ys) := by
  rfl
variable (C)
def levenshtein (xs : List α) (ys : List β) : δ :=
  let ⟨r, w⟩ := suffixLevenshtein C xs ys
  r[0]
variable {C}
theorem suffixLevenshtein_nil_nil : (suffixLevenshtein C [] []).1 = [0] := by
  rfl
theorem List.eq_of_length_one (x : List α) (w : x.length = 1) :
    have : 0 < x.length := lt_of_lt_of_eq Nat.zero_lt_one w.symm
    x = [x[0]] := by
  match x, w with
  | [r], _ => rfl
theorem suffixLevenshtein_nil' (ys : List β) :
    (suffixLevenshtein C [] ys).1 = [levenshtein C [] ys] :=
  List.eq_of_length_one _ (suffixLevenshtein_length [] _)
theorem suffixLevenshtein_cons₂ (xs : List α) (y ys) :
    suffixLevenshtein C xs (y :: ys) = (impl C xs) y (suffixLevenshtein C xs ys) :=
  rfl
theorem suffixLevenshtein_cons₁_aux {α} {x y : { l : List α // 0 < l.length }}
    (w₀ : x.1[0]'x.2 = y.1[0]'y.2) (w : x.1.tail = y.1.tail) : x = y := by
  match x, y with
  | ⟨hx :: tx, _⟩, ⟨hy :: ty, _⟩ => simp_all
theorem suffixLevenshtein_cons₁
    (x : α) (xs ys) :
    suffixLevenshtein C (x :: xs) ys =
      ⟨levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1, by simp⟩ := by
  induction ys with
  | nil =>
    dsimp [levenshtein, suffixLevenshtein]
  | cons y ys ih =>
    apply suffixLevenshtein_cons₁_aux
    · rfl
    · rw [suffixLevenshtein_cons₂ (x :: xs), ih, impl_cons]
      · rfl
      · simp [suffixLevenshtein_length]
theorem suffixLevenshtein_cons₁_fst (x : α) (xs ys) :
    (suffixLevenshtein C (x :: xs) ys).1 =
      levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1 := by
  simp [suffixLevenshtein_cons₁]
theorem suffixLevenshtein_cons_cons_fst_get_zero
    (x : α) (xs y ys) (w : 0 < (suffixLevenshtein C (x :: xs) (y :: ys)).val.length) :
    (suffixLevenshtein C (x :: xs) (y :: ys)).1[0]'w =
      let ⟨dx, _⟩ := suffixLevenshtein C xs (y :: ys)
      let ⟨dy, _⟩ := suffixLevenshtein C (x :: xs) ys
      let ⟨dxy, _⟩ := suffixLevenshtein C xs ys
      min
        (C.delete x + dx[0])
        (min
          (C.insert y + dy[0])
          (C.substitute x y + dxy[0])) := by
  conv =>
    lhs
    dsimp only [suffixLevenshtein_cons₂]
  simp only [suffixLevenshtein_cons₁]
  rw [impl_cons_fst_zero]
  rfl
theorem suffixLevenshtein_eq_tails_map (xs ys) :
    (suffixLevenshtein C xs ys).1 = xs.tails.map fun xs' => levenshtein C xs' ys := by
  induction xs with
  | nil =>
    simp only [List.map, suffixLevenshtein_nil']
  | cons x xs ih =>
    simp only [List.map, suffixLevenshtein_cons₁, ih]
@[simp]
theorem levenshtein_nil_nil : levenshtein C [] [] = 0 := by
  simp [levenshtein, suffixLevenshtein]
@[simp]
theorem levenshtein_nil_cons (y) (ys) :
    levenshtein C [] (y :: ys) = C.insert y + levenshtein C [] ys := by
  dsimp (config := { unfoldPartialApp := true }) [levenshtein, suffixLevenshtein, impl]
  congr
  rw [List.getLast_eq_getElem]
  congr
  rw [show (List.length _) = 1 from _]
  induction ys <;> simp
@[simp]
theorem levenshtein_cons_nil (x : α) (xs : List α) :
    levenshtein C (x :: xs) [] = C.delete x + levenshtein C xs [] :=
  rfl
@[simp]
theorem levenshtein_cons_cons
    (x : α) (xs : List α) (y : β) (ys : List β) :
    levenshtein C (x :: xs) (y :: ys) =
      min (C.delete x + levenshtein C xs (y :: ys))
        (min (C.insert y + levenshtein C (x :: xs) ys)
          (C.substitute x y + levenshtein C xs ys)) :=
  suffixLevenshtein_cons_cons_fst_get_zero ..