import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
open scoped Topology InnerProductSpace
namespace ContinuousLinearMapWOT
variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
@[ext]
lemma ext_inner {A B : E →WOT[𝕜] F} (h : ∀ x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) : A = B := by
  rw [ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y
open Filter in
lemma tendsto_iff_forall_inner_apply_tendsto [CompleteSpace F] {α : Type*} {l : Filter α}
    {f : α → E →WOT[𝕜] F} {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜) := by
  simp_rw [tendsto_iff_forall_dual_apply_tendsto, ← InnerProductSpace.toDual_apply]
  exact .symm <| forall_congr' fun _ ↦
    Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ ↦ Iff.rfl
lemma le_nhds_iff_forall_inner_apply_le_nhds [CompleteSpace F] {l : Filter (E →WOT[𝕜] F)}
    {A : E →WOT[𝕜] F} : l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫_𝕜) ≤ 𝓝 (⟪y, A x⟫_𝕜) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)
end ContinuousLinearMapWOT