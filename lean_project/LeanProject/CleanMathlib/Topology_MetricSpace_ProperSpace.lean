import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.IsLUB
open Set Filter
universe u v w
variable {α : Type u} {β : Type v} {X ι : Type*}
section ProperSpace
open Metric
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)
export ProperSpace (isCompact_closedBall)
theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall
instance Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (x : α) (r : ℝ) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
variable [PseudoMetricSpace α]
instance (priority := 100) secondCountable_of_proper [ProperSpace α] :
    SecondCountableTopology α := by
  suffices SigmaCompactSpace α from EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩
theorem ProperSpace.of_isCompact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_ball
    (closedBall_subset_closedBall <| le_max_left _ _)⟩
theorem ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β → ℝ}
    (hr : Tendsto r l atTop) (hc : ∀ᶠ i in l, IsCompact (closedBall x (r i))) :
    ProperSpace α where
  isCompact_closedBall a r :=
    let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
    hci.of_isClosed_subset isClosed_ball <| closedBall_subset_closedBall' hir
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun _ _ => isClosed_ball.isCompact⟩
instance (priority := 100) locallyCompact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  .of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _
@[nolint defLemma, deprecated (since := "2024-11-13")]
alias locally_compact_of_proper := locallyCompact_of_proper
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨fun {f} hf => by
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩
instance prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)
instance pi_properSpace {π : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (π b)]
    [h : ∀ b, ProperSpace (π b)] : ProperSpace (∀ b, π b) := by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
end ProperSpace
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Additive X) := ‹ProperSpace X›
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Multiplicative X) := ‹ProperSpace X›
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace Xᵒᵈ := ‹ProperSpace X›