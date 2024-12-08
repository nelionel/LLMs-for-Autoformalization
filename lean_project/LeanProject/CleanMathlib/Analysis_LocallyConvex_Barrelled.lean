import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Baire.Lemmas
open Filter Topology Set ContinuousLinearMap
section defs
class BarrelledSpace (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p
theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type*} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp
theorem Seminorm.continuous_iSup
    {ι : Sort*} {𝕜 E : Type*} [NormedField 𝕜]  [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i) := by
  rw [← Seminorm.coe_iSup_eq bdd]
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply
end defs
section TVS_anyField
variable {α ι κ 𝕜₁ 𝕜₂ E F : Type*} [Nonempty κ] [NontriviallyNormedField 𝕜₁]
    [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F]
instance BaireSpace.instBarrelledSpace [TopologicalSpace E] [TopologicalAddGroup E]
    [ContinuousConstSMul 𝕜₁ E] [BaireSpace E] :
    BarrelledSpace 𝕜₁ E where
  continuous_of_lowerSemicontinuous := by
    intro p hp
    have h₁ : ∀ n : ℕ, IsClosed (p.closedBall (0 : E) n) := fun n ↦ by
      simpa [p.closedBall_zero_eq] using hp.isClosed_preimage n
    have h₂ : (⋃ n : ℕ, p.closedBall (0 : E) n) = univ :=
      eq_univ_of_forall fun x ↦ mem_iUnion.mpr (exists_nat_ge <| p (x - 0))
    rcases nonempty_interior_of_iUnion_of_closed h₁ h₂ with ⟨n, ⟨x, hxn⟩⟩
    refine Seminorm.continuous' (r := n + n) ?_
    rw [p.closedBall_zero_eq] at hxn ⊢
    have hxn' : p x ≤ n := by convert interior_subset hxn
    rw [mem_interior_iff_mem_nhds, ← map_add_left_nhds_zero] at hxn
    filter_upwards [hxn] with y hy
    calc p y = p (x + y - x) := by rw [add_sub_cancel_left]
      _ ≤ p (x + y) + p x := map_sub_le_add _ _ _
      _ ≤ n + n := add_le_add hy hxn'
namespace WithSeminorms
variable [UniformSpace E] [UniformSpace F] [UniformAddGroup E] [UniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)
include hq
protected theorem banach_steinhaus (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup (toLinearMap ∘ 𝓕)).mpr ?_
  intro k
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩
variable [ContinuousSMul 𝕜₂ F]
protected def continuousLinearMapOfTendsto (hq : WithSeminorms q)
    [T2Space F] {l : Filter α} [l.IsCountablyGenerated]
    [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F} (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F where
  toLinearMap := linearMapOfTendsto _ _ h
  cont := by
    rcases l.exists_seq_tendsto with ⟨u, hu⟩
    refine (h.comp hu).continuous_of_equicontinuous (hq.banach_steinhaus ?_).equicontinuous
    intro k x
    rw [tendsto_pi_nhds] at h
    exact (((hq.continuous_seminorm k).tendsto _).comp <| (h x).comp hu).bddAbove_range
end WithSeminorms
end TVS_anyField