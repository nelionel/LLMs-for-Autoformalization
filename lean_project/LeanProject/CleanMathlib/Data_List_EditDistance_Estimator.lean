import Mathlib.Data.List.EditDistance.Bounds
import Mathlib.Order.Estimator
variable {α : Type*} {β δ : Type} [CanonicallyLinearOrderedAddCommMonoid δ]
  (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β)
structure LevenshteinEstimator' : Type where
  pre_rev : List β
  suff : List β
  split : pre_rev.reverse ++ suff = ys
  distances : {r : List δ // 0 < r.length}
  distances_eq : distances = suffixLevenshtein C xs suff
  bound : δ × ℕ
  bound_eq : bound = match pre_rev with
    | [] => (distances.1[0]'(distances.2), ys.length)
    | _ => (List.minimum_of_length_pos distances.2, suff.length)
instance : EstimatorData (Thunk.mk fun _ => (levenshtein C xs ys, ys.length))
    (LevenshteinEstimator' C xs ys) where
  bound e := e.bound
  improve e := match e.pre_rev, e.split with
    | [], _ => none
    | y :: ys, split => some
      { pre_rev := ys
        suff := y :: e.suff
        split := by simpa using split
        distances := Levenshtein.impl C xs y e.distances
        distances_eq := e.distances_eq ▸ suffixLevenshtein_eq xs y e.suff
        bound := _
        bound_eq := rfl }
instance estimator' :
    Estimator (Thunk.mk fun _ => (levenshtein C xs ys, ys.length))
      (LevenshteinEstimator' C xs ys) where
  bound_le e := match e.pre_rev, e.split, e.bound_eq with
  | [], split, eq => by
    simp only [List.reverse_nil, List.nil_append] at split
    rw [e.distances_eq] at eq
    simp only [← List.get_eq_getElem] at eq
    rw [split] at eq
    exact eq.le
  | y :: t, split, eq => by
    rw [e.distances_eq] at eq
    simp only at eq
    dsimp [EstimatorData.bound]
    rw [eq]
    simp only [← split]
    constructor
    · simp only [List.minimum_of_length_pos_le_iff]
      exact suffixLevenshtein_minimum_le_levenshtein_append _ _ _
    · exact (List.sublist_append_right _ _).length_le
  improve_spec e := by
    dsimp [EstimatorData.improve]
    match e.pre_rev, e.split, e.bound_eq, e.distances_eq with
    | [], split, eq, _ =>
      simp only [List.reverse_nil, List.nil_append] at split
      rw [e.distances_eq] at eq
      simp only [← List.get_eq_getElem] at eq
      rw [split] at eq
      exact eq
    | [y], split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff, List.reverse_nil, List.nil_append]
      right
      have b_eq :
          e.bound = (List.minimum_of_length_pos e.distances.property, List.length e.suff) := by
        simpa using b_eq
      rw [b_eq]
      constructor
      · refine (?_ : _ ≤ _).trans (List.minimum_of_length_pos_le_getElem _)
        simp only [List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos, d_eq]
        apply le_suffixLevenshtein_cons_minimum
      · simp [← split]
    | y₁ :: y₂ :: t, split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff]
      right
      have b_eq :
          e.bound = (List.minimum_of_length_pos e.distances.property, List.length e.suff) := by
        simpa using b_eq
      rw [b_eq]
      constructor
      · simp only [d_eq, List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos]
        apply le_suffixLevenshtein_cons_minimum
      · exact Nat.lt.base _
def LevenshteinEstimator : Type _ :=
  Estimator.fst (Thunk.mk fun _ => (levenshtein C xs ys, ys.length)) (LevenshteinEstimator' C xs ys)
instance [∀ a : δ × ℕ, WellFoundedGT { x // x ≤ a }] :
    Estimator (Thunk.mk fun _ => levenshtein C xs ys) (LevenshteinEstimator C xs ys) :=
  Estimator.fstInst (Thunk.mk fun _ => _) (Thunk.mk fun _ => _) (estimator' C xs ys)
instance (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) :
    Bot (LevenshteinEstimator C xs ys) where
  bot :=
  { inner :=
    { pre_rev := ys.reverse
      suff := []
      split := by simp
      distances_eq := rfl
      bound_eq := rfl } }