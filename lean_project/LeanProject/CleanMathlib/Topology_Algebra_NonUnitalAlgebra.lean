import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Topology.Algebra.Module.Basic
namespace NonUnitalSubalgebra
section Semiring
variable {R A : Type*} [CommSemiring R] [TopologicalSpace A]
variable [NonUnitalSemiring A] [Module R A] [TopologicalSemiring A]
variable [ContinuousConstSMul R A]
instance instTopologicalSemiring (s : NonUnitalSubalgebra R A) : TopologicalSemiring s :=
  s.toNonUnitalSubsemiring.instTopologicalSemiring
def topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A :=
  { s.toNonUnitalSubsemiring.topologicalClosure, s.toSubmodule.topologicalClosure with
    carrier := _root_.closure (s : Set A) }
theorem le_topologicalClosure (s : NonUnitalSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
theorem isClosed_topologicalClosure (s : NonUnitalSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure
theorem topologicalClosure_minimal (s : NonUnitalSubalgebra R A) {t : NonUnitalSubalgebra R A}
    (h : s ≤ t) (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  s.toNonUnitalSubsemiring.nonUnitalCommSemiringTopologicalClosure hs
end Semiring
section Ring
variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [TopologicalRing A]
variable [ContinuousConstSMul R A]
instance instTopologicalRing (s : NonUnitalSubalgebra R A) : TopologicalRing s :=
  s.toNonUnitalSubring.instTopologicalRing
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }
end Ring
end NonUnitalSubalgebra
namespace NonUnitalAlgebra
open NonUnitalSubalgebra
variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [TopologicalSpace A] [TopologicalSemiring A] [ContinuousConstSMul R A]
def elemental (x : A) : NonUnitalSubalgebra R A :=
  adjoin R {x} |>.topologicalClosure
namespace elemental
@[aesop safe apply (rule_sets := [SetLike])]
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x
variable {R} in
theorem le_of_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A)) (hx : x ∈ s) :
    elemental R x ≤ s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs
variable {R} in
theorem le_iff_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩
instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _
instance [T2Space A] {x : A} : NonUnitalCommSemiring (elemental R x) :=
  nonUnitalCommSemiringTopologicalClosure _
    letI : NonUnitalCommSemiring (adjoin R {x}) :=
      NonUnitalAlgebra.adjoinNonUnitalCommSemiringOfComm R fun y hy z hz => by
        rw [Set.mem_singleton_iff] at hy hz
        rw [hy, hz]
    fun _ _ => mul_comm _ _
instance {R A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [TopologicalSpace A] [TopologicalRing A] [ContinuousConstSMul R A]
    [T2Space A] {x : A} : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A]
    [TopologicalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
end elemental
end NonUnitalAlgebra