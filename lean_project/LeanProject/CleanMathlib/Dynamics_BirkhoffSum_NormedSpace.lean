import Mathlib.Analysis.RCLike.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
open Function Set Filter
open scoped Topology ENNReal Uniformity
section
variable {α E : Type*}
theorem Function.IsFixedPt.tendsto_birkhoffAverage
    (R : Type*) [DivisionSemiring R] [CharZero R]
    [AddCommMonoid E] [TopologicalSpace E] [Module R E]
    {f : α → α} {x : α} (h : f.IsFixedPt x) (g : α → E) :
    Tendsto (birkhoffAverage R f g · x) atTop (𝓝 (g x)) :=
  tendsto_const_nhds.congr' <| (eventually_ne_atTop 0).mono fun _n hn ↦
    (h.birkhoffAverage_eq R g hn).symm
variable [NormedAddCommGroup E]
theorem dist_birkhoffSum_apply_birkhoffSum (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffSum f g n (f x)) (birkhoffSum f g n x) = dist (g (f^[n] x)) (g x) := by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]
theorem dist_birkhoffSum_birkhoffSum_le (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffSum f g n x) (birkhoffSum f g n y) ≤
      ∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y)) :=
  dist_sum_sum_le _ _ _
variable (𝕜 : Type*) [RCLike 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]
theorem dist_birkhoffAverage_birkhoffAverage (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) =
      dist (birkhoffSum f g n x) (birkhoffSum f g n y) / n := by
  simp [birkhoffAverage, dist_smul₀, div_eq_inv_mul]
theorem dist_birkhoffAverage_birkhoffAverage_le (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) ≤
      (∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
  (dist_birkhoffAverage_birkhoffAverage _ _ _ _ _ _).trans_le <| by
    gcongr; apply dist_birkhoffSum_birkhoffSum_le
theorem dist_birkhoffAverage_apply_birkhoffAverage (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffAverage 𝕜 f g n (f x)) (birkhoffAverage 𝕜 f g n x) =
      dist (g (f^[n] x)) (g x) / n := by
  simp [dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum]
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage {f : α → α} {g : α → E} {x : α}
    (h : Bornology.IsBounded (range (g <| f^[·] x))) :
    Tendsto (fun n ↦ birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) := by
  rcases Metric.isBounded_range_iff.1 h with ⟨C, hC⟩
  have : Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n ↦ ?_) this
  rw [← dist_eq_norm, dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  exact hC n 0
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage' {g : α → E}
    (h : Bornology.IsBounded (range g)) (f : α → α) (x : α) :
    Tendsto (fun n ↦ birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) :=
  tendsto_birkhoffAverage_apply_sub_birkhoffAverage _ <| h.subset <| range_comp_subset_range _ _
end
variable (𝕜 : Type*) {X E : Type*}
  [PseudoEMetricSpace X] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : X → X} {g : X → E} {l : X → E}
theorem uniformEquicontinuous_birkhoffAverage (hf : LipschitzWith 1 f) (hg : UniformContinuous g) :
    UniformEquicontinuous (birkhoffAverage 𝕜 f g) := by
  refine Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right.2 fun ε hε ↦ ?_
  rcases (uniformity_basis_edist_le.uniformContinuous_iff Metric.uniformity_basis_dist_le).1 hg ε hε
    with ⟨δ, hδ₀, hδε⟩
  refine mem_uniformity_edist.2 ⟨δ, hδ₀, fun {x y} h n ↦ ?_⟩
  calc
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y)
      ≤ (∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
      dist_birkhoffAverage_birkhoffAverage_le ..
    _ ≤ (∑ _k ∈ Finset.range n, ε) / n := by
      gcongr
      refine hδε _ _ ?_
      simpa using (hf.iterate _).edist_le_mul_of_le h.le
    _ = n * ε / n := by simp
    _ ≤ ε := by
      rcases eq_or_ne n 0 with hn | hn <;> field_simp [hn, hε.le, mul_div_cancel_left₀]
theorem isClosed_setOf_tendsto_birkhoffAverage
    (hf : LipschitzWith 1 f) (hg : UniformContinuous g) (hl : Continuous l) :
    IsClosed {x | Tendsto (birkhoffAverage 𝕜 f g · x) atTop (𝓝 (l x))} :=
  (uniformEquicontinuous_birkhoffAverage 𝕜 hf hg).equicontinuous.isClosed_setOf_tendsto hl