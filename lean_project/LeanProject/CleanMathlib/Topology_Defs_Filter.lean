import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IrreducibleDef
assert_not_exists Ultrafilter
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
open Filter
open scoped Topology
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s
@[inherit_doc]
scoped[Topology] notation "𝓝[" s "] " x:100 => nhdsWithin x s
scoped[Topology] notation3 "𝓝[≠] " x:100 =>
  nhdsWithin x (@singleton _ (Set _) Set.instSingletonSet x)ᶜ
scoped[Topology] notation3 "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)
scoped[Topology] notation3 "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)
scoped[Topology] notation3 "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)
scoped[Topology] notation3 "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)
def nhdsSet (s : Set X) : Filter X :=
  sSup (nhds '' s)
@[inherit_doc] scoped[Topology] notation "𝓝ˢ" => nhdsSet
def exterior (s : Set X) : Set X := (𝓝ˢ s).ker
@[fun_prop]
def ContinuousAt (f : X → Y) (x : X) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
@[fun_prop]
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))
@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x
def Specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y
@[inherit_doc]
infixl:300 " ⤳ " => Specializes
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
variable (X)
def specializationPreorder : Preorder X :=
  { Preorder.lift (OrderDual.toDual ∘ 𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }
def inseparableSetoid : Setoid X := { Setoid.comap 𝓝 ⊥ with r := Inseparable }
def SeparationQuotient := Quotient (inseparableSetoid X)
variable {X}
section Lim
noncomputable def lim [Nonempty X] (f : Filter X) : X :=
  Classical.epsilon fun x => f ≤ 𝓝 x
noncomputable def limUnder {α : Type*} [Nonempty X] (f : Filter α) (g : α → X) : X :=
  lim (f.map g)
end Lim
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
variable (X) in
class CompactSpace : Prop where
  isCompact_univ : IsCompact (Set.univ : Set X)
variable (X) in
class NoncompactSpace : Prop where
  noncompact_univ : ¬IsCompact (Set.univ : Set X)
class WeaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_compact_mem_nhds (x : X) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x
export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)
class LocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
class LocallyCompactPair (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  exists_mem_nhds_isCompact_mapsTo : ∀ {f : X → Y} {x : X} {s : Set Y},
    Continuous f → s ∈ 𝓝 (f x) → ∃ K ∈ 𝓝 x, IsCompact K ∧ Set.MapsTo f K s
export LocallyCompactPair (exists_mem_nhds_isCompact_mapsTo)
variable (X) in
def Filter.cocompact : Filter X :=
  ⨅ (s : Set X) (_ : IsCompact s), 𝓟 sᶜ
variable (X) in
def Filter.coclosedCompact : Filter X :=
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsCompact s), 𝓟 sᶜ