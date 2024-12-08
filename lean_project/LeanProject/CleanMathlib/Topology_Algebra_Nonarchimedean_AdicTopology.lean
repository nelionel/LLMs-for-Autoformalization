import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.UniformRing
variable {R : Type*} [CommRing R]
open Set TopologicalAddGroup Submodule Filter
open Topology Pointwise
namespace Ideal
theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.id.map_eq_id, map_id, le_inf_iff] using this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i by
        simpa only [smul_top_eq_map, Algebra.id.map_eq_id, map_id] using this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices ∀ i : ℕ, ∃ j : ℕ, (↑(I ^ j) * ↑(I ^ j) : Set R) ⊆ (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.id.map_eq_id, map_id] using this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }
def ringFilterBasis (I : Ideal R) :=
  I.adic_basis.toRing_subgroups_basis.toRingFilterBasis
def adicTopology (I : Ideal R) : TopologicalSpace R :=
  (adic_basis I).topology
theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology :=
  I.adic_basis.toRing_subgroups_basis.nonarchimedean
theorem hasBasis_nhds_zero_adic (I : Ideal R) :
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun _n : ℕ => True) fun n =>
      ((I ^ n : Ideal R) : Set R) :=
  ⟨by
    intro U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) ⊆ U := by simpa using h
      exact ⟨i, trivial, h⟩
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩
theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun _n : ℕ => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) := by
  letI := I.adicTopology
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
theorem adic_module_basis :
    I.ringFilterBasis.SubmodulesBasis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
          ⟨smul_mono_left <| pow_le_pow_right (le_max_left i j),
            smul_mono_left <| pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a ∈ I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))
def openAddSubgroup (n : ℕ) : @OpenAddSubgroup R _ I.adicTopology := by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp [smul_top_eq_map, Algebra.id.map_eq_id, map_id, restrictScalars_self]
end Ideal
section IsAdic
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology
theorem isAdic_iff [top : TopologicalSpace R] [TopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (∀ n : ℕ, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        ∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J ^ n : Ideal R) : Set R) ⊆ s := by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    letI := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply TopologicalAddGroup.ext
    · apply @TopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      letI := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩
variable [TopologicalSpace R] [TopologicalRing R]
theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) := by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    cases' h.right V hV with m hm
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul, Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left
theorem is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [TopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A := by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]
end IsAdic
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R
namespace WithIdeal
variable (R)
variable [WithIdeal R]
instance (priority := 100) : TopologicalSpace R :=
  i.adicTopology
instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _
instance (priority := 100) : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R
instance (priority := 100) : UniformAddGroup R :=
  comm_topologicalAddGroup_is_uniform
def topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicModuleTopology M
example : NonarchimedeanRing R := by infer_instance
example : TopologicalRing (UniformSpace.Completion R) := by infer_instance
example (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance
example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance
example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _
end WithIdeal