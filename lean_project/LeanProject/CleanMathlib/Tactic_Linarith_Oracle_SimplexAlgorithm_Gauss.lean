import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes
namespace Linarith.SimplexAlgorithm.Gauss
abbrev GaussM (n m : Nat) (matType : Nat → Nat → Type) := StateT (matType n m) Lean.CoreM
variable {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
def findNonzeroRow (rowStart col : Nat) : GaussM n m matType <| Option Nat := do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return .none
def getTableauImp : GaussM n m matType <| Tableau matType := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]
  let mut row : Nat := 0
  let mut col : Nat := 0
  while row < n && col < m do
    Lean.Core.checkSystem decl_name%.toString
    match ← findNonzeroRow row col with
    | .none =>
      free := free.push col
      col := col + 1
      continue
    | .some rowToSwap =>
      modify fun mat => swapRows mat row rowToSwap
    modify fun mat => divideRow mat row mat[(row, col)]!
    for i in [:n] do
      if i == row then
        continue
      let coef := (← get)[(i, col)]!
      if coef != 0 then
        modify fun mat => subtractRow mat row i coef
    basic := basic.push col
    row := row + 1
    col := col + 1
  for i in [col:m] do
    free := free.push i
  let ansMatrix : matType basic.size free.size := ← do
    let vals := getValues (← get) |>.filterMap fun (i, j, v) =>
      if j == basic[i]! then
        .none
      else
        .some (i, free.findIdx? (· == j) |>.get!, -v)
    return ofValues vals
  return ⟨basic, free, ansMatrix⟩
def getTableau (A : matType n m) : Lean.CoreM (Tableau matType) := do
  return (← getTableauImp.run A).fst
end Linarith.SimplexAlgorithm.Gauss