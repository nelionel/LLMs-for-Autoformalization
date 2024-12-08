import Mathlib.Order.ConditionallyCompleteLattice.Basic
open Set
variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] {f : α → β} {s : Set α}
theorem MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Monotone g ∧ EqOn f g s := by
  classical
    rcases hl with ⟨a, ha⟩
    have hu' : ∀ x, BddAbove (f '' (Iic x ∩ s)) := fun x =>
      hu.mono (image_subset _ inter_subset_right)
    let g : α → β := fun x => if Disjoint (Iic x) s then a else sSup (f '' (Iic x ∩ s))
    have hgs : EqOn f g s := by
      intro x hx
      simp only [g]
      have : IsGreatest (Iic x ∩ s) x := ⟨⟨right_mem_Iic, hx⟩, fun y hy => hy.1⟩
      rw [if_neg this.nonempty.not_disjoint,
        ((h.mono inter_subset_right).map_isGreatest this).csSup_eq]
    refine ⟨g, fun x y hxy => ?_, hgs⟩
    by_cases hx : Disjoint (Iic x) s <;> by_cases hy : Disjoint (Iic y) s <;>
      simp only [g, if_pos, if_neg, not_false_iff, *, refl]
    · rcases not_disjoint_iff_nonempty_inter.1 hy with ⟨z, hz⟩
      exact le_csSup_of_le (hu' _) (mem_image_of_mem _ hz) (ha <| mem_image_of_mem _ hz.2)
    · exact (hx <| hy.mono_left <| Iic_subset_Iic.2 hxy).elim
    · rw [not_disjoint_iff_nonempty_inter] at hx hy
      refine csSup_le_csSup (hu' _) (hx.image _) (image_subset _ ?_)
      exact inter_subset_inter_left _ (Iic_subset_Iic.2 hxy)
theorem AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Antitone g ∧ EqOn f g s :=
  h.dual_right.exists_monotone_extension hu hl