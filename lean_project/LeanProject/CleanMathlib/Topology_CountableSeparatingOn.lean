import Mathlib.Order.Filter.CountableSeparatingOn
import Mathlib.Topology.Separation.Basic
variable {X : Type*}
open Set TopologicalSpace
instance [TopologicalSpace X] {s : Set X} [T0Space s] [SecondCountableTopology s] :
    HasCountableSeparatingOn X IsOpen s := by
  suffices HasCountableSeparatingOn s IsOpen univ from .of_subtype fun _ ↦ isOpen_induced_iff.1
  refine ⟨⟨countableBasis s, countable_countableBasis _, fun _ ↦ isOpen_of_mem_countableBasis,
    fun x _ y _ h ↦ ?_⟩⟩
  exact ((isBasis_countableBasis _).inseparable_iff.2 h).eq
instance [TopologicalSpace X] {s : Set X} [h : HasCountableSeparatingOn X IsOpen s] :
    HasCountableSeparatingOn X IsClosed s :=
  let ⟨S, hSc, hSo, hS⟩ := h.1
  ⟨compl '' S, hSc.image _, forall_mem_image.2 fun U hU ↦ (hSo U hU).isClosed_compl,
    fun x hx y hy h ↦ hS x hx y hy fun _U hU ↦ not_iff_not.1 <| h _ (mem_image_of_mem _ hU)⟩