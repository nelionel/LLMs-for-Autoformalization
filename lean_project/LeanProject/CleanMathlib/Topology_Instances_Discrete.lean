import Mathlib.Topology.Order.Basic
open Order Set TopologicalSpace Filter
variable {α : Type*} [TopologicalSpace α]
instance (priority := 100) DiscreteTopology.firstCountableTopology [DiscreteTopology α] :
    FirstCountableTopology α where
  nhds_generated_countable := by rw [nhds_discrete]; exact isCountablyGenerated_pure
instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable
    [hd : DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (iUnion_of_singleton α)
@[deprecated DiscreteTopology.secondCountableTopology_of_countable (since := "2024-03-11")]
theorem DiscreteTopology.secondCountableTopology_of_encodable {α : Type*}
    [TopologicalSpace α] [DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  DiscreteTopology.secondCountableTopology_of_countable
theorem LinearOrder.bot_topologicalSpace_eq_generateFrom {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a } := by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm
@[deprecated (since := "2024-11-02")]
alias bot_topologicalSpace_eq_generateFrom_of_pred_succOrder :=
  LinearOrder.bot_topologicalSpace_eq_generateFrom
theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h ↦ ⟨?_⟩, fun h ↦ .of_predOrder_succOrder⟩
  rw [h.eq_bot, LinearOrder.bot_topologicalSpace_eq_generateFrom]
@[deprecated (since := "2024-11-02")]
alias discreteTopology_iff_orderTopology_of_pred_succ' :=
  discreteTopology_iff_orderTopology_of_pred_succ
instance OrderTopology.of_discreteTopology [LinearOrder α] [PredOrder α] [SuccOrder α]
    [DiscreteTopology α] : OrderTopology α :=
  discreteTopology_iff_orderTopology_of_pred_succ.mp ‹_›