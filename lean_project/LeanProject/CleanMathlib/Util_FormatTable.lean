import Mathlib.Data.String.Defs
inductive Alignment where
  | left
  | right
  | center
deriving Inhabited, BEq
def String.justify (s : String) (a : Alignment) (width : Nat) : String :=
  match a with
  | Alignment.left => s.rightpad width
  | Alignment.right => s.leftpad width
  | Alignment.center =>
    let pad := (width - s.length) / 2
    String.replicate pad ' ' ++ s ++ String.replicate (width - s.length - pad) ' '
def formatTable (headers : Array String) (table : Array (Array String))
    (alignments : Option (Array Alignment) := none) :
    String := Id.run do
  let alignments := alignments.getD (Array.mkArray headers.size Alignment.left)
  let escapedHeaders := headers.map (fun header => header.replace "|" "\\|")
  let escapedTable := table.map (fun row => row.map (fun cell => cell.replace "|" "\\|"))
  let mut widths := escapedHeaders.map (·.length)
  for row in escapedTable do
    for i in [0:widths.size] do
      widths := widths.set! i (max widths[i]! ((row[i]?.map (·.length)).getD 0))
  let paddedHeaders := escapedHeaders.mapIdx fun i h => h.rightpad widths[i]!
  let paddedTable := escapedTable.map fun row => row.mapIdx fun i cell =>
    cell.justify alignments[i]! widths[i]!
  let headerLine := "| " ++ String.intercalate " | " (paddedHeaders.toList) ++ " |"
  let separatorLine :=
    "| "
    ++ String.intercalate " | "
        (((widths.zip alignments).map fun ⟨w, a⟩ =>
              match w, a with
              | 0, _ => ""
              | 1, _ => "-"
              | _ + 2, Alignment.left => ":" ++ String.replicate (w-1) '-'
              | _ + 2, Alignment.right => String.replicate (w-1) '-' ++ ":"
              | _ + 2, Alignment.center => ":" ++ String.replicate (w-2) '-' ++ ":"
              ).toList)
    ++ " |"
  let rowLines := paddedTable.map (fun row => "| " ++ String.intercalate " | " (row.toList) ++ " |")
  return String.intercalate "\n" (headerLine :: separatorLine :: rowLines.toList)