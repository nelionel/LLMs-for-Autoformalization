import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
open Filter Finset Function Bornology
open scoped Topology
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
theorem LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E]
    (f : E →ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E →L[𝕜] LinearMap.eqLocus f 1)
    (hg_proj : ∀ x : LinearMap.eqLocus f 1, g x = x)
    (hg_ker : (LinearMap.ker g : Set E) ⊆ closure (LinearMap.range (f - 1))) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 (g x)) := by
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y, g y = 0 ∧ ∃ z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  suffices Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0) by
    have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOf_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_mem_range.2 fun x ↦ ?_) this (hg_ker hy)
  have : IsBounded (Set.range (_root_.id <| f^[·] x)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_mem_range.2 fun n ↦ by
      have H : f^[n] 0 = 0 := iterate_map_zero (f : E →+ E) n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : ∀ n x y, f^[n] (x - y) = f^[n] x - f^[n] y := iterate_map_sub (f : E →+ E)
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this
variable [InnerProductSpace 𝕜 E] [CompleteSpace E]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y
theorem ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (f : E →L[𝕜] E)
    (hf : ‖f‖ ≤ 1) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop
      (𝓝 <| orthogonalProjection (LinearMap.eqLocus f 1) x) := by
  apply (f : E →ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure (f.lipschitz.weaken hf)
  · exact orthogonalProjection_mem_subspace_eq_self (K := LinearMap.eqLocus f 1)
  · clear x
    rw [ker_orthogonalProjection, ← Submodule.topologicalClosure_coe, SetLike.coe_subset_coe,
      ← Submodule.orthogonal_orthogonal_eq_closure]
    refine Submodule.orthogonal_le fun x hx ↦ eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ?_ ?_
    · simpa using f.le_of_opNorm_le hf x
    · have : ∀ y, ⟪f y, x⟫ = ⟪y, x⟫ := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
      simp [this, ← norm_sq_eq_inner]