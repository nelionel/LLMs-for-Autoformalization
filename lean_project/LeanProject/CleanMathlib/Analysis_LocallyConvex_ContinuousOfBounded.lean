import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.RCLike.Basic
open TopologicalSpace Bornology Filter Topology Pointwise
variable {𝕜 𝕜' E F : Type*}
variable [AddCommGroup E] [UniformSpace E] [UniformAddGroup E]
variable [AddCommGroup F] [UniformSpace F]
section NontriviallyNormedField
variable [UniformAddGroup F]
variable [NontriviallyNormedField 𝕜] [Module 𝕜 E] [Module 𝕜 F] [ContinuousSMul 𝕜 E]
def LinearMap.clmOfExistsBoundedImage (f : E →ₗ[𝕜] F)
    (h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜 (f '' V)) : E →L[𝕜] F :=
  ⟨f, by
    refine continuous_of_continuousAt_zero f ?_
    rw [continuousAt_def, f.map_zero]
    intro U hU
    rcases h with ⟨V, hV, h⟩
    rcases (h hU).exists_pos with ⟨r, hr, h⟩
    rcases NormedField.exists_lt_norm 𝕜 r with ⟨x, hx⟩
    specialize h x hx.le
    have x_ne := norm_pos_iff.mp (hr.trans hx)
    have : x⁻¹ • V ⊆ f ⁻¹' U :=
      calc
        x⁻¹ • V ⊆ x⁻¹ • f ⁻¹' (f '' V) := Set.smul_set_mono (Set.subset_preimage_image (⇑f) V)
        _ ⊆ x⁻¹ • f ⁻¹' (x • U) := Set.smul_set_mono (Set.preimage_mono h)
        _ = f ⁻¹' (x⁻¹ • x • U) := by
          ext
          simp only [Set.mem_inv_smul_set_iff₀ x_ne, Set.mem_preimage, LinearMap.map_smul]
        _ ⊆ f ⁻¹' U := by rw [inv_smul_smul₀ x_ne _]
    refine mem_of_superset ?_ this
    rwa [set_smul_mem_nhds_zero_iff (inv_ne_zero x_ne)]⟩
theorem LinearMap.clmOfExistsBoundedImage_coe {f : E →ₗ[𝕜] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜 (f '' V)} :
    (f.clmOfExistsBoundedImage h : E →ₗ[𝕜] F) = f :=
  rfl
@[simp]
theorem LinearMap.clmOfExistsBoundedImage_apply {f : E →ₗ[𝕜] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜 (f '' V)} {x : E} :
    f.clmOfExistsBoundedImage h x = f x :=
  rfl
end NontriviallyNormedField
section RCLike
open TopologicalSpace Bornology
variable [FirstCountableTopology E]
variable [RCLike 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
variable [RCLike 𝕜'] [Module 𝕜' F] [ContinuousSMul 𝕜' F]
variable {σ : 𝕜 →+* 𝕜'}
theorem LinearMap.continuousAt_zero_of_locally_bounded (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : ContinuousAt f 0 := by
  by_contra h
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩
  simp only [_root_.id] at bE
  have bE' : (𝓝 (0 : E)).HasBasis (fun x : ℕ => x ≠ 0) fun n : ℕ => (n : 𝕜)⁻¹ • b n := by
    refine bE.1.to_hasBasis ?_ ?_
    · intro n _
      use n + 1
      simp only [Ne, Nat.succ_ne_zero, not_false_iff, Nat.cast_add, Nat.cast_one, true_and]
      have h : b (n + 1) ⊆ b n := bE.2 (by simp)
      refine _root_.trans ?_ h
      rintro y ⟨x, hx, hy⟩
      rw [← hy]
      refine (bE1 (n + 1)).2.smul_mem ?_ hx
      have h' : 0 < (n : ℝ) + 1 := n.cast_add_one_pos
      rw [norm_inv, ← Nat.cast_one, ← Nat.cast_add, RCLike.norm_natCast, Nat.cast_add,
        Nat.cast_one, inv_le_comm₀ h' zero_lt_one]
      simp
    intro n hn
    have hcont : ContinuousAt (fun x : E => (n : 𝕜) • x) 0 :=
      (continuous_const_smul (n : 𝕜)).continuousAt
    simp only [ContinuousAt, map_zero, smul_zero] at hcont
    rw [bE.1.tendsto_left_iff] at hcont
    rcases hcont (b n) (bE1 n).1 with ⟨i, _, hi⟩
    refine ⟨i, trivial, fun x hx => ⟨(n : 𝕜) • x, hi hx, ?_⟩⟩
    simp [← mul_smul, hn]
  rw [ContinuousAt, map_zero, bE'.tendsto_iff (nhds_basis_balanced 𝕜' F)] at h
  push_neg at h
  rcases h with ⟨V, ⟨hV, -⟩, h⟩
  simp only [_root_.id, forall_true_left] at h
  choose! u hu hu' using h
  have h_tendsto : Tendsto (fun n : ℕ => (n : 𝕜) • u n) atTop (𝓝 (0 : E)) := by
    apply bE.tendsto
    intro n
    by_cases h : n = 0
    · rw [h, Nat.cast_zero, zero_smul]
      exact mem_of_mem_nhds (bE.1.mem_of_mem <| by trivial)
    rcases hu n h with ⟨y, hy, hu1⟩
    convert hy
    rw [← hu1, ← mul_smul]
    simp only [h, mul_inv_cancel₀, Ne, Nat.cast_eq_zero, not_false_iff, one_smul]
  have h_bounded : IsVonNBounded 𝕜 (Set.range fun n : ℕ => (n : 𝕜) • u n) :=
    h_tendsto.cauchySeq.totallyBounded_range.isVonNBounded 𝕜
  rcases (hf _ h_bounded hV).exists_pos with ⟨r, hr, h'⟩
  cases' exists_nat_gt r with n hn
  have h1 : r ≤ ‖(n : 𝕜')‖ := by
    rw [RCLike.norm_natCast]
    exact hn.le
  have hn' : 0 < ‖(n : 𝕜')‖ := lt_of_lt_of_le hr h1
  rw [norm_pos_iff, Ne, Nat.cast_eq_zero] at hn'
  have h'' : f (u n) ∈ V := by
    simp only [Set.image_subset_iff] at h'
    specialize h' (n : 𝕜') h1 (Set.mem_range_self n)
    simp only [Set.mem_preimage, LinearMap.map_smulₛₗ, map_natCast] at h'
    rcases h' with ⟨y, hy, h'⟩
    apply_fun fun y : F => (n : 𝕜')⁻¹ • y at h'
    simp only [hn', inv_smul_smul₀, Ne, Nat.cast_eq_zero, not_false_iff] at h'
    rwa [← h']
  exact hu' n hn' h''
theorem LinearMap.continuous_of_locally_bounded [UniformAddGroup F] (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : Continuous f :=
  (uniformContinuous_of_continuousAt_zero f <| f.continuousAt_zero_of_locally_bounded hf).continuous
end RCLike