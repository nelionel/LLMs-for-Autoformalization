import Mathlib.Init
import Batteries.Data.Rat.Basic
import Std.Data.HashMap.Basic
namespace Linarith.SimplexAlgorithm
class UsableInSimplexAlgorithm (α : Nat → Nat → Type) where
  getElem {n m : Nat} (mat : α n m) (i j : Nat) : Rat
  setElem {n m : Nat} (mat : α n m) (i j : Nat) (v : Rat) : α n m
  getValues {n m : Nat} (mat : α n m) : List (Nat × Nat × Rat)
  ofValues {n m : Nat} (values : List (Nat × Nat × Rat)) : α n m
  swapRows {n m : Nat} (mat : α n m) (i j : Nat) : α n m
  subtractRow {n m : Nat} (mat : α n m) (i j : Nat) (coef : Rat) : α n m
  divideRow {n m : Nat} (mat : α n m) (i : Nat) (coef : Rat) : α n m
export UsableInSimplexAlgorithm (setElem getValues ofValues swapRows subtractRow divideRow)
instance (n m : Nat) (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] :
    GetElem (matType n m) (Nat × Nat) Rat fun _ p => p.1 < n ∧ p.2 < m where
  getElem mat p _ := UsableInSimplexAlgorithm.getElem mat p.1 p.2
structure DenseMatrix (n m : Nat) where
  data : Array (Array Rat)
instance : UsableInSimplexAlgorithm DenseMatrix where
  getElem mat i j := mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.modify i fun row => row.set! j v⟩
  getValues mat :=
    mat.data.zipWithIndex.foldl (init := []) fun acc (row, i) =>
      let rowVals := Array.toList <| row.zipWithIndex.filterMap fun (v, j) =>
        if v != 0 then
          .some (i, j, v)
        else
          .none
      rowVals ++ acc
  ofValues {n m : Nat} vals : DenseMatrix _ _ := Id.run do
    let mut data : Array (Array Rat) := Array.mkArray n <| Array.mkArray m 0
    for ⟨i, j, v⟩ in vals do
      data := data.modify i fun row => row.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      row.zipWith mat.data[i]! fun x y => x - coef * y
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩
structure SparseMatrix (n m : Nat) where
  data : Array <| Std.HashMap Nat Rat
instance : UsableInSimplexAlgorithm SparseMatrix where
  getElem mat i j := mat.data[i]!.getD j 0
  setElem mat i j v :=
    if v == 0 then
      ⟨mat.data.modify i fun row => row.erase j⟩
    else
      ⟨mat.data.modify i fun row => row.insert j v⟩
  getValues mat :=
    mat.data.zipWithIndex.foldl (init := []) fun acc (row, i) =>
      let rowVals := row.toList.map fun (j, v) => (i, j, v)
      rowVals ++ acc
  ofValues {n _ : Nat} vals := Id.run do
    let mut data : Array (Std.HashMap Nat Rat) := Array.mkArray n .empty
    for ⟨i, j, v⟩ in vals do
      if v != 0 then
        data := data.modify i fun row => row.insert j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData := mat.data.modify j fun row =>
      mat.data[i]!.fold (fun cur k val =>
        let newVal := (cur.getD k 0) - coef * val
        if newVal != 0 then cur.insert k newVal else cur.erase k
      ) row
    ⟨newData⟩
  divideRow mat i coef :=
    let newData : Array (Std.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩
structure Tableau (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] where
  basic : Array Nat
  free : Array Nat
  mat : matType basic.size free.size
end Linarith.SimplexAlgorithm