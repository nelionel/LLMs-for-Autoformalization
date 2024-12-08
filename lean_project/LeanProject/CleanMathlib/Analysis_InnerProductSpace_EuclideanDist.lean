import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
open scoped Topology
open Set
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [TopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
noncomputable section
open Module
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
namespace Euclidean
nonrec def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)
def closedBall (x : E) (r : ℝ) : Set E :=
  {y | dist y x ≤ r}
def ball (x : E) (r : ℝ) : Set E :=
  {y | dist y x < r}
theorem ball_eq_preimage (x : E) (r : ℝ) :
    ball x r = toEuclidean ⁻¹' Metric.ball (toEuclidean x) r :=
  rfl
theorem closedBall_eq_preimage (x : E) (r : ℝ) :
    closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r :=
  rfl
theorem ball_subset_closedBall {x : E} {r : ℝ} : ball x r ⊆ closedBall x r := fun _ (hy : _ < r) =>
  le_of_lt hy
theorem isOpen_ball {x : E} {r : ℝ} : IsOpen (ball x r) :=
  Metric.isOpen_ball.preimage toEuclidean.continuous
theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r :=
  Metric.mem_ball_self hr
theorem closedBall_eq_image (x : E) (r : ℝ) :
    closedBall x r = toEuclidean.symm '' Metric.closedBall (toEuclidean x) r := by
  rw [toEuclidean.image_symm_eq_preimage, closedBall_eq_preimage]
nonrec theorem isCompact_closedBall {x : E} {r : ℝ} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous
theorem isClosed_closedBall {x : E} {r : ℝ} : IsClosed (closedBall x r) :=
  isCompact_closedBall.isClosed
nonrec theorem closure_ball (x : E) {r : ℝ} (h : r ≠ 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage, ← toEuclidean.preimage_closure, closure_ball (toEuclidean x) h,
    closedBall_eq_preimage]
nonrec theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s)
    (h : s ⊆ ball x R) : ∃ r ∈ Ioo 0 R, s ⊆ ball x r := by
  rw [ball_eq_preimage, ← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (toEuclidean.isClosed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩
theorem nhds_basis_closedBall {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (closedBall x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _
theorem closedBall_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closedBall x r ∈ 𝓝 x :=
  nhds_basis_closedBall.mem_of_mem hr
theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (ball x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _
theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr
end Euclidean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f g : F → G} {n : ℕ∞}
theorem ContDiff.euclidean_dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun x => Euclidean.dist (f x) (g x) := by
  simp only [Euclidean.dist]
  apply ContDiff.dist ℝ
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]