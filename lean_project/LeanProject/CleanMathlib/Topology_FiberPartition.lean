import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Logic.Function.FiberPartition
open Function
variable {S Y : Type*} (f : S → Y)
namespace TopologicalSpace.Fiber
variable [TopologicalSpace S]
@[simps apply]
def sigmaIsoHom : C((x : Fiber f) × x.val, S) where
  toFun | ⟨a, x⟩ => x.val
lemma sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]
lemma sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩
def sigmaIncl (a : Fiber f) : C(a.val, S) where
  toFun x := x.val
def sigmaInclIncl {X : Type*} (g : Y → X) (a : Fiber (g ∘ f))
    (b : Fiber (f ∘ (sigmaIncl (g ∘ f) a))) :
    C(b.val, (Fiber.mk f (b.preimage).val).val) where
  toFun x := ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image, Fiber.mk_image, this, ← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩
variable (l : LocallyConstant S Y) [CompactSpace S]
instance (x : Fiber l) : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  rw [← isCompact_iff_compactSpace, ← hy]
  exact (l.2.isClosed_fiber _).isCompact
instance : Finite (Fiber l) :=
  have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _
end TopologicalSpace.Fiber