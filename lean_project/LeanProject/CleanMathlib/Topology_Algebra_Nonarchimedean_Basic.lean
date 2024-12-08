import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
open Topology
open scoped Pointwise
class NonarchimedeanAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends
  TopologicalAddGroup G : Prop where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : G), ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U
@[to_additive]
class NonarchimedeanGroup (G : Type*) [Group G] [TopologicalSpace G] extends TopologicalGroup G :
  Prop where
  is_nonarchimedean : ∀ U ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ U
class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] extends TopologicalRing R :
  Prop where
  is_nonarchimedean : ∀ U ∈ 𝓝 (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U
instance (priority := 100) NonarchimedeanRing.to_nonarchimedeanAddGroup (R : Type*) [Ring R]
    [TopologicalSpace R] [t : NonarchimedeanRing R] : NonarchimedeanAddGroup R :=
  { t with }
namespace NonarchimedeanGroup
variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [TopologicalGroup H]
variable {K : Type*} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]
@[to_additive]
theorem nonarchimedean_of_emb (f : G →* H) (emb : IsOpenEmbedding f) : NonarchimedeanGroup H :=
  { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U ∈ 𝓝 (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }
@[to_additive NonarchimedeanAddGroup.prod_subset "An open neighborhood of the identity in
the cartesian product of two nonarchimedean groups contains the cartesian product of
an open neighborhood in each group."]
theorem prod_subset {U} (hU : U ∈ 𝓝 (1 : G × K)) :
    ∃ (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) ⊆ U := by
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  cases' is_nonarchimedean _ hU₁ with V hV
  cases' is_nonarchimedean _ hU₂ with W hW
  use V; use W
  rw [Set.prod_subset_iff]
  intro x hX y hY
  exact Set.Subset.trans (Set.prod_mono hV hW) h (Set.mem_sep hX hY)
@[to_additive NonarchimedeanAddGroup.prod_self_subset "An open neighborhood of the identity in
the cartesian square of a nonarchimedean group contains the cartesian square of
an open neighborhood in the group."]
theorem prod_self_subset {U} (hU : U ∈ 𝓝 (1 : G × G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ×ˢ (V : Set G) ⊆ U :=
  let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine Set.Subset.trans (Set.prod_mono ?_ ?_) ‹_› <;> simp⟩
@[to_additive "The cartesian product of two nonarchimedean groups is nonarchimedean."]
instance : NonarchimedeanGroup (G × K) where
  is_nonarchimedean _ hU :=
    let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩
end NonarchimedeanGroup
namespace NonarchimedeanRing
open NonarchimedeanAddGroup
variable {R S : Type*}
variable [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]
variable [Ring S] [TopologicalSpace S] [NonarchimedeanRing S]
instance : NonarchimedeanRing (R × S) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean
theorem left_mul_subset (U : OpenAddSubgroup R) (r : R) :
    ∃ V : OpenAddSubgroup R, r • (V : Set R) ⊆ U :=
  ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_mul_left r), (U : Set R).image_preimage_subset _⟩
theorem mul_subset (U : OpenAddSubgroup R) : ∃ V : OpenAddSubgroup R, (V : Set R) * V ⊆ U := by
  let ⟨V, H⟩ := prod_self_subset <| (U.isOpen.preimage continuous_mul).mem_nhds <| by
    simpa only [Set.mem_preimage, Prod.snd_zero, mul_zero] using U.zero_mem
  use V
  rintro v ⟨a, ha, b, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [SetLike.mem_coe]
  exact hy
end NonarchimedeanRing