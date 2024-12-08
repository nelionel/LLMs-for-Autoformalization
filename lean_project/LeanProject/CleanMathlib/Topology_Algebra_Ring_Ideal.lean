import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Defs
open Topology
section Ring
variable {R : Type*} [TopologicalSpace R] [Ring R] [TopologicalRing R]
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }
@[simp]
theorem Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I :=
  rfl
theorem Ideal.closure_eq_of_isClosed (I : Ideal R) (hI : IsClosed (I : Set R)) : I.closure = I :=
  SetLike.ext' hI.closure_eq
end Ring
section CommRing
variable {R : Type*} [TopologicalSpace R] [CommRing R] (N : Ideal R)
open Ideal.Quotient
instance topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N) :=
  instTopologicalSpaceQuotient
variable [TopologicalRing R]
theorem QuotientRing.isOpenMap_coe : IsOpenMap (mk N) :=
  QuotientAddGroup.isOpenMap_coe
theorem QuotientRing.isOpenQuotientMap_mk : IsOpenQuotientMap (mk N) :=
  QuotientAddGroup.isOpenQuotientMap_mk
theorem QuotientRing.isQuotientMap_coe_coe : IsQuotientMap fun p : R × R => (mk N p.1, mk N p.2) :=
  ((isOpenQuotientMap_mk N).prodMap (isOpenQuotientMap_mk N)).isQuotientMap
@[deprecated (since := "2024-10-22")]
alias QuotientRing.quotientMap_coe_coe := QuotientRing.isQuotientMap_coe_coe
instance topologicalRing_quotient : TopologicalRing (R ⧸ N) where
  __ := QuotientAddGroup.instTopologicalAddGroup _
  continuous_mul := (QuotientRing.isQuotientMap_coe_coe N).continuous_iff.2 <|
    continuous_quot_mk.comp continuous_mul
end CommRing