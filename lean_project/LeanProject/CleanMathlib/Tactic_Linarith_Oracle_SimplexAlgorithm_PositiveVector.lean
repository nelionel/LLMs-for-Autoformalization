import Lean.Meta.Basic
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.SimplexAlgorithm
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Gauss
namespace Linarith.SimplexAlgorithm
variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
def stateLP {n m : Nat} (A : matType n m) (strictIndexes : List Nat) : matType (n + 2) (m + 3) :=
  let objectiveRow : List (Nat × Nat × Rat) :=
    (0, 0, -1) :: strictIndexes.map fun idx => (0, idx + 2, 1)
  let constraintRow : List (Nat × Nat × Rat) :=
    [(1, 1, 1), (1, m + 2, -1)] ++ (List.range m).map (fun i => (1, i + 2, 1))
  let valuesA := getValues A |>.map fun (i, j, v) => (i + 2, j + 2, v)
  ofValues (objectiveRow ++ constraintRow ++ valuesA)
def extractSolution (tableau : Tableau matType) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.mkArray (tableau.basic.size + tableau.free.size - 3) 0
  for i in [1:tableau.basic.size] do
    ans := ans.set! (tableau.basic[i]! - 2) <| tableau.mat[(i, tableau.free.size - 1)]!
  return ans
def findPositiveVector {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
    (A : matType n m) (strictIndexes : List Nat) : Lean.Meta.MetaM <| Array Rat := do
  let B := stateLP A strictIndexes
  let initTableau ← Gauss.getTableau B
  let res ← runSimplexAlgorithm.run initTableau
  if res.fst.isOk then
    return extractSolution res.snd
  else
    throwError "Simplex Algorithm failed"
end SimplexAlgorithm
end Linarith