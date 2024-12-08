import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Algebra.Module.Submodule.Pointwise
open Set Filter Function Lattice
open Topology Filter Pointwise
structure RingSubgroupsBasis {A ι : Type*} [Ring A] (B : ι → AddSubgroup A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
  leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (x * ·) ⁻¹' B i
  rightMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (· * x) ⁻¹' B i
namespace RingSubgroupsBasis
variable {A ι : Type*} [Ring A]
theorem of_comm {A ι : Type*} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := fun x i ↦ (leftMul x i).imp fun j hj ↦ by simpa only [mul_comm] using hj }
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    cases' hB.mul i with k hk
    use B k
    constructor
    · use k
    · exact hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.leftMul x₀ i with k hk
    use B k
    constructor
    · use k
    · exact hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.rightMul x₀ i with k hk
    use B k
    constructor
    · use k
    · exact hk
variable [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B)
theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V ∈ hB.toRingFilterBasis.toAddGroupFilterBasis ↔ ∃ i, V = B i :=
  Iff.rfl
theorem mem_addGroupFilterBasis (i) : (B i : Set A) ∈ hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology
theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩
theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a ∈ B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp only [image_add_left, neg_add_eq_sub]
      ext b
      simp
    · rintro ⟨i, hi⟩
      use B i
      constructor
      · use i
      · rw [image_subset_iff]
        rintro b b_in
        apply hi
        simpa using b_in⟩
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩
end RingSubgroupsBasis
variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
structure SubmodulesRingBasis (B : ι → Submodule R A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  leftMul : ∀ (a : A) (i), ∃ j, a • B j ≤ B i
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
namespace SubmodulesRingBasis
variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup := by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b ∈ B j)
  exact hj ⟨b, b_in, rfl⟩
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology
end SubmodulesRingBasis
variable {M : Type*} [AddCommGroup M] [Module R M]
structure SubmodulesBasis [TopologicalSpace R] (B : ι → Submodule R M) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i
namespace SubmodulesBasis
variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)
def toModuleFilterBasis : ModuleFilterBasis R M where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ
    constructor
    · exact univ_mem
    · use B i
      constructor
      · use i
      · rintro _ ⟨a, -, m, hm, rfl⟩
        exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro m
      exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology 
  { (B i).toAddSubgroup with
    isOpen' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rfl⟩
        exact (B i).add_mem a_in b_in }
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩
library_note "nonarchimedean non instances"
end SubmodulesBasis
section
variable [TopologicalSpace R] {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : ∀ (m : A) (i : ι), ∀ᶠ a : R in 𝓝 0, a • m ∈ B i)
include hB hsmul
theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }
example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl
end
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι → Submodule R M) :
    Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (· • m) ⁻¹' B i
theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _ BR.topology B :=
  let _ := BR.topology 
  { inter := hB.inter
    smul := by
      letI := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)