import Mathlib.RepresentationTheory.FDRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Invariants
noncomputable section
universe u
open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation Module
variable {k : Type u} [Field k]
namespace FDRep
section Monoid
variable {G : Type u} [Monoid G]
def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]
@[simp]
theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]
@[simp]
theorem char_tensor (V W : FDRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g; convert trace_tensorProduct' (V.ρ g) (W.ρ g)
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm
end Monoid
section Group
variable {G : Type u} [Group G]
@[simp]
theorem char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]
@[simp]
theorem char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)
@[simp]
theorem char_linHom (V W : FDRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dualTensorIsoLinHom _ _), char_tensor, Pi.mul_apply, char_dual]
variable [Fintype G] [Invertible (Fintype.card G : k)]
theorem average_char_eq_finrank_invariants (V : FDRep k G) :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]
end Group
section Orthogonality
variable {G : Grp.{u}} [IsAlgClosed k]
open scoped Classical
variable [Fintype G] [Invertible (Fintype.card G : k)]
theorem char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  conv_lhs =>
    enter [2, 2, g]
    rw [mul_comm, ← char_dual, ← Pi.mul_apply, ← char_tensor]
    rw [char_iso (FDRep.dualTensorIsoLinHom W.ρ V)]
  rw [average_char_eq_finrank_invariants]
  rw [show (of (linHom W.ρ V.ρ)).ρ = linHom W.ρ V.ρ from FDRep.of_ρ (linHom W.ρ V.ρ)]
  erw [(linHom.invariantsEquivFDRepHom W V).finrank_eq] 
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
end Orthogonality
end FDRep