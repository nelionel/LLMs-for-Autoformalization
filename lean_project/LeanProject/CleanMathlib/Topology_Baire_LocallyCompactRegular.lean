import Mathlib.Topology.Sets.Compacts
open TopologicalSpace Set
instance (priority := 100) BaireSpace.of_t2Space_locallyCompactSpace {X : Type*}
    [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X] : BaireSpace X := by
  constructor
  intro f ho hd
  rw [dense_iff_inter_open]
  intro U U_open U_nonempty
  obtain ⟨K, hK_anti, hKf, hKU⟩ : ∃ K : ℕ → PositiveCompacts X,
      (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, closure ↑(K (n + 1)) ⊆ f n) ∧ closure ↑(K 0) ⊆ U := by
    rcases U_open.exists_positiveCompacts_closure_subset U_nonempty with ⟨K₀, hK₀⟩
    have : ∀ (n) (K : PositiveCompacts X),
        ∃ K' : PositiveCompacts X, closure ↑K' ⊆ f n ∩ interior K := by
      refine fun n K ↦ ((ho n).inter isOpen_interior).exists_positiveCompacts_closure_subset ?_
      rw [inter_comm]
      exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
    choose K_next hK_next using this
    use Nat.rec K₀ K_next
    refine ⟨fun n ↦ ?_, fun n ↦ (hK_next n _).trans inter_subset_left, hK₀⟩
    exact subset_closure.trans <| (hK_next _ _).trans <|
      inter_subset_right.trans interior_subset
  have hK_subset : (⋂ n, closure (K n) : Set X) ⊆ U ∩ ⋂ n, f n := fun x hx ↦ by
    simp only [mem_iInter, mem_inter_iff] at hx ⊢
    exact ⟨hKU <| hx 0, fun n ↦ hKf n <| hx (n + 1)⟩
  have hK_nonempty : (⋂ n, closure (K n) : Set X).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => closure_mono <| hK_anti n) (fun n => (K n).nonempty.closure)
      (K 0).isCompact.closure fun n => isClosed_closure
  exact hK_nonempty.mono hK_subset