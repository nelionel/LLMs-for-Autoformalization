import Mathlib.Data.Vector.Basic
namespace Mathlib
namespace Vector
variable {α β σ φ : Type*} {n : ℕ} {x : α} {s : σ} (xs : Vector α n)
def snoc : Vector α n → α → Vector α (n+1) :=
  fun xs x => append xs (x ::ᵥ Vector.nil)
section Simp
variable {y : α}
@[simp]
theorem snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y) :=
  rfl
@[simp]
theorem snoc_nil : (nil.snoc x) = x ::ᵥ nil :=
  rfl
@[simp]
theorem reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).snoc x := by
  cases xs
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  congr
@[simp]
theorem reverse_snoc : reverse (xs.snoc x) = x ::ᵥ (reverse xs) := by
  cases xs
  simp only [reverse, snoc, cons, toList_mk]
  congr
  simp [toList, Vector.append, Append.append]
theorem replicate_succ_to_snoc (val : α) :
    replicate (n+1) val = (replicate n val).snoc val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ]
    conv => rhs; rw [replicate_succ]
    rw [snoc_cons, ih]
end Simp
section Induction
@[elab_as_elim]
def revInductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C xs → C (xs.snoc x)) :
    C v :=
  cast (by simp) <| inductionOn
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)
@[elab_as_elim]
def revInductionOn₂ {C : ∀ {n : ℕ}, Vector α n → Vector β n → Sort*} {n : ℕ}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (ys : Vector β n) (x : α) (y : β),
      C xs ys → C (xs.snoc x) (ys.snoc y)) :
    C v w :=
  cast (by simp) <| inductionOn₂
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
      cast (by simp) <| snoc xs.reverse ys.reverse x y r)
@[elab_as_elim]
def revCasesOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C (xs.snoc x)) :
    C v :=
  revInductionOn v nil fun xs x _ => snoc xs x
end Induction
section Simp
@[simp]
theorem map_snoc {f : α → β} : map f (xs.snoc x) = (map f xs).snoc (f x) := by
  induction xs <;> simp_all
@[simp]
theorem mapAccumr_nil {f : α → σ → σ × β} {s : σ} : mapAccumr f Vector.nil s = (s, Vector.nil) :=
  rfl
@[simp]
theorem mapAccumr_snoc {f : α → σ → σ × β} {s : σ} :
    mapAccumr f (xs.snoc x) s
    = let q := f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs
  · rfl
  · simp [*]
variable (ys : Vector β n)
@[simp]
theorem map₂_snoc {f : α → β → σ} {y : β} :
    map₂ f (xs.snoc x) (ys.snoc y) = (map₂ f xs ys).snoc (f x y) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
@[simp]
theorem mapAccumr₂_nil {f : α → β → σ → σ × φ} :
    mapAccumr₂ f Vector.nil Vector.nil s = (s, Vector.nil) :=
  rfl
@[simp]
theorem mapAccumr₂_snoc (f : α → β → σ → σ × φ) (x : α) (y : β) :
    mapAccumr₂ f (xs.snoc x) (ys.snoc y) s
    = let q := f x y s
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
end Simp
end Vector
end Mathlib