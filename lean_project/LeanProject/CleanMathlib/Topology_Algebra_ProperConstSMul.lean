import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Maps.Proper.Basic
class ProperConstVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  isProperMap_vadd (c : M) : IsProperMap ((c +ᵥ ·) : X → X)
@[to_additive]
class ProperConstSMul (M X : Type*) [SMul M X] [TopologicalSpace X] : Prop where
  isProperMap_smul (c : M) : IsProperMap ((c • ·) : X → X)
@[to_additive "`(c +ᵥ ·)` is a proper map."]
theorem isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSpace X]
    [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X → X) := h.1 c
@[to_additive "The preimage of a compact set under `(c +ᵥ ·)` is a compact set."]
theorem IsCompact.preimage_smul {M X : Type*} [SMul M X] [TopologicalSpace X]
    [ProperConstSMul M X] {s : Set X} (hs : IsCompact s) (c : M) : IsCompact ((c • ·) ⁻¹' s) :=
  (isProperMap_smul c X).isCompact_preimage hs
@[to_additive]
instance (priority := 100) {M X : Type*} [SMul M X] [TopologicalSpace X] [ContinuousConstSMul M X]
    [T2Space X] [CompactSpace X] : ProperConstSMul M X :=
  ⟨fun c ↦ (continuous_const_smul c).isProperMap⟩
@[to_additive]
instance (priority := 100) {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] : ProperConstSMul G X :=
  ⟨fun c ↦ (Homeomorph.smul c).isProperMap⟩
instance {M X Y : Type*}
    [SMul M X] [TopologicalSpace X] [ProperConstSMul M X]
    [SMul M Y] [TopologicalSpace Y] [ProperConstSMul M Y] :
    ProperConstSMul M (X × Y) :=
  ⟨fun c ↦ (isProperMap_smul c X).prodMap (isProperMap_smul c Y)⟩
instance {M ι : Type*} {X : ι → Type*}
    [∀ i, SMul M (X i)] [∀ i, TopologicalSpace (X i)] [∀ i, ProperConstSMul M (X i)] :
    ProperConstSMul M (∀ i, X i) :=
  ⟨fun c ↦ .pi_map fun i ↦ isProperMap_smul c (X i)⟩