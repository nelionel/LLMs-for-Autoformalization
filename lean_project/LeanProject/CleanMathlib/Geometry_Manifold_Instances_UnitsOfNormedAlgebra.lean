import Mathlib.Geometry.Manifold.Algebra.LieGroup
noncomputable section
open scoped Manifold
local notation "∞" => (⊤ : ℕ∞)
namespace Units
variable {R : Type*} [NormedRing R] [CompleteSpace R]
instance : ChartedSpace R Rˣ :=
  isOpenEmbedding_val.singletonChartedSpace
theorem chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl
theorem chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ :=
  rfl
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]
instance : SmoothManifoldWithCorners 𝓘(𝕜, R) Rˣ :=
  isOpenEmbedding_val.singleton_smoothManifoldWithCorners
lemma contMDiff_val {m : ℕ∞} : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) m (val : Rˣ → R) :=
  contMDiff_isOpenEmbedding Units.isOpenEmbedding_val
instance : LieGroup 𝓘(𝕜, R) Rˣ where
  smooth_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
      (fun x : R × R => x.1 * x.2) ∘ (fun x : Rˣ × Rˣ => (x.1, x.2)) := by ext; simp
    rw [this]
    have : ContMDiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R × R) ∞
      (fun x : Rˣ × Rˣ => ((x.1 : R), (x.2 : R))) :=
      (contMDiff_val.comp contMDiff_fst).prod_mk_space (contMDiff_val.comp contMDiff_snd)
    refine ContMDiff.comp ?_ this
    rw [contMDiff_iff_contDiff]
    exact contDiff_mul
  smooth_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this, ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ring_inverse _ _
end Units