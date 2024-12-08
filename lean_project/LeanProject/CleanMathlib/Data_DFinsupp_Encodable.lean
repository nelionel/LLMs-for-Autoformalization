import Mathlib.Data.DFinsupp.Defs
import Mathlib.Logic.Equiv.List
variable {ι : Type*} {α : ι → Type*} [∀ i, Zero (α i)]
instance [Encodable ι] [∀ i, Encodable (α i)] [∀ i (x : α i), Decidable (x ≠ 0)] :
    Encodable (Π₀ i, α i) :=
  letI : DecidableEq ι := Encodable.decidableEqOfEncodable _
  letI : ∀ s : Finset ι, Encodable (∀ i : s, {x : α i // x ≠ 0}) := fun _ ↦
    .ofEquiv _ <| .piCongrLeft' _ Encodable.fintypeEquivFin
  .ofEquiv _ DFinsupp.sigmaFinsetFunEquiv
instance [Countable ι] [∀ i, Countable (α i)] : Countable (Π₀ i, α i) := by
  classical
    let _ := Encodable.ofCountable ι
    let _ := fun i ↦ Encodable.ofCountable (α i)
    infer_instance