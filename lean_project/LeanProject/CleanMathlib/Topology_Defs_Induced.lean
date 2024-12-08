import Mathlib.Topology.Basic
open Set
open scoped Topology
namespace TopologicalSpace
variable {X Y : Type*}
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t
def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
end TopologicalSpace
namespace Topology
variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
structure RestrictGenTopology (S : Set (Set X)) : Prop where
  isOpen_of_forall_induced (u : Set X) : (∀ s ∈ S, IsOpen ((↑) ⁻¹' u : Set s)) → IsOpen u
@[mk_iff]
structure IsInducing (f : X → Y) : Prop where
  eq_induced : tX = tY.induced f
@[deprecated (since := "2024-10-28")] alias Inducing := IsInducing
@[mk_iff]
structure IsEmbedding (f : X → Y) extends IsInducing f : Prop where
  injective : Function.Injective f
@[deprecated (since := "2024-10-26")]
alias Embedding := IsEmbedding
@[mk_iff]
structure IsOpenEmbedding (f : X → Y) extends IsEmbedding f : Prop where
  isOpen_range : IsOpen <| range f
@[deprecated (since := "2024-10-18")]
alias OpenEmbedding := IsOpenEmbedding
@[mk_iff]
structure IsClosedEmbedding (f : X → Y) extends IsEmbedding f : Prop where
  isClosed_range : IsClosed <| range f
@[deprecated (since := "2024-10-20")]
alias ClosedEmbedding := IsClosedEmbedding
@[mk_iff isQuotientMap_iff']
structure IsQuotientMap {X : Type*} {Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) : Prop where
  surjective : Function.Surjective f
  eq_coinduced : tY = tX.coinduced f
@[deprecated (since := "2024-10-22")]
alias QuotientMap := IsQuotientMap
end Topology