import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
open Filter Metric Set Topology
open scoped BoundedContinuousFunction
namespace TopologicalSpace
section RegularSpace
variable (X : Type*) [TopologicalSpace X] [RegularSpace X] [SecondCountableTopology X]
theorem exists_isInducing_l_infty : ∃ f : X → ℕ →ᵇ ℝ, IsInducing f := by
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩
  let s : Set (Set X × Set X) := { UV ∈ B ×ˢ B | closure UV.1 ⊆ UV.2 }
  haveI : Encodable s := ((hBc.prod hBc).mono inter_subset_left).toEncodable
  letI : TopologicalSpace s := ⊥
  haveI : DiscreteTopology s := ⟨rfl⟩
  rsuffices ⟨f, hf⟩ : ∃ f : X → s →ᵇ ℝ, IsInducing f
  · exact ⟨fun x => (f x).extend (Encodable.encode' s) 0,
      (BoundedContinuousFunction.isometry_extend (Encodable.encode' s)
        (0 : ℕ →ᵇ ℝ)).isEmbedding.isInducing.comp hf⟩
  have hd : ∀ UV : s, Disjoint (closure UV.1.1) UV.1.2ᶜ :=
    fun UV => disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ Tendsto ε cofinite (𝓝 0) := by
    rcases posSumOfEncodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩
    refine ⟨ε, fun UV => ⟨ε0 UV, ?_⟩, hεc.summable.tendsto_cofinite_zero⟩
    exact (le_hasSum hεc UV fun _ _ => (ε0 _).le).trans hc1
  have : ∀ UV : s, ∃ f : C(X, ℝ),
      EqOn f 0 UV.1.1 ∧ EqOn f (fun _ => ε UV) UV.1.2ᶜ ∧ ∀ x, f x ∈ Icc 0 (ε UV) := by
    intro UV
    rcases exists_continuous_zero_one_of_isClosed isClosed_closure
        (hB.isOpen UV.2.1.2).isClosed_compl (hd UV) with
      ⟨f, hf₀, hf₁, hf01⟩
    exact ⟨ε UV • f, fun x hx => by simp [hf₀ (subset_closure hx)], fun x hx => by simp [hf₁ hx],
      fun x => ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε using this
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1 :=
    fun UV x => Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)
  set F : X → s →ᵇ ℝ := fun x =>
    ⟨⟨fun UV => f UV x, continuous_of_discreteTopology⟩, 1,
      fun UV₁ UV₂ => Real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩
  have hF : ∀ x UV, F x UV = f UV x := fun _ _ => rfl
  refine ⟨F, isInducing_iff_nhds.2 fun x => le_antisymm ?_ ?_⟩
  · 
    refine (nhds_basis_closedBall.comap _).ge_iff.2 fun δ δ0 => ?_
    have h_fin : { UV : s | δ ≤ ε UV }.Finite := by simpa only [← not_lt] using hε (gt_mem_nhds δ0)
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ := by
      refine (eventually_all_finite h_fin).2 fun UV _ => ?_
      exact (f UV).continuous.tendsto x (closedBall_mem_nhds _ δ0)
    refine this.mono fun y hy => (BoundedContinuousFunction.dist_le δ0.le).2 fun UV => ?_
    rcases le_total δ (ε UV) with hle | hle
    exacts [hy _ hle, (Real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa [sub_zero])]
  · 
    refine ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_hasBasis).2 ?_
    rintro V ⟨hVB, hxV⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    refine ⟨ε UV, (ε01 UV).1, fun y (hy : dist (F y) (F x) < ε UV) => ?_⟩
    replace hy : dist (F y UV) (F x UV) < ε UV :=
      (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hy
    contrapose! hy
    rw [hF, hF, hfε UV hy, hf0 UV hxU, Pi.zero_apply, dist_zero_right]
    exact le_abs_self _
@[deprecated (since := "2024-10-28")] alias exists_inducing_l_infty := exists_isInducing_l_infty
instance (priority := 90) PseudoMetrizableSpace.of_regularSpace_secondCountableTopology :
    PseudoMetrizableSpace X :=
  let ⟨_, hf⟩ := exists_isInducing_l_infty X
  hf.pseudoMetrizableSpace
end RegularSpace
variable (X : Type*) [TopologicalSpace X] [T3Space X] [SecondCountableTopology X]
theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, IsEmbedding f :=
  let ⟨f, hf⟩ := exists_isInducing_l_infty X; ⟨f, hf.isEmbedding⟩
instance (priority := 90) metrizableSpace_of_t3_secondCountable : MetrizableSpace X :=
  let ⟨_, hf⟩ := exists_embedding_l_infty X
  hf.metrizableSpace
@[nolint defLemma, deprecated (since := "2024-11-13")] alias
metrizableSpace_of_t3_second_countable := metrizableSpace_of_t3_secondCountable
end TopologicalSpace