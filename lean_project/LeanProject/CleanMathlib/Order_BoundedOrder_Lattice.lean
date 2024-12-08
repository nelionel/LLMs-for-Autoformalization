import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice
open Function OrderDual
universe u v
variable {α : Type u} {β : Type v}
section SemilatticeSupTop
variable [SemilatticeSup α] [OrderTop α]
theorem top_sup_eq (a : α) : ⊤ ⊔ a = ⊤ :=
  sup_of_le_left le_top
theorem sup_top_eq (a : α) : a ⊔ ⊤ = ⊤ :=
  sup_of_le_right le_top
end SemilatticeSupTop
section SemilatticeSupBot
variable [SemilatticeSup α] [OrderBot α] {a b : α}
theorem bot_sup_eq (a : α) : ⊥ ⊔ a = a :=
  sup_of_le_right bot_le
theorem sup_bot_eq (a : α) : a ⊔ ⊥ = a :=
  sup_of_le_left bot_le
@[simp]
theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by rw [eq_bot_iff, sup_le_iff]; simp
end SemilatticeSupBot
section SemilatticeInfTop
variable [SemilatticeInf α] [OrderTop α] {a b : α}
lemma top_inf_eq (a : α) : ⊤ ⊓ a = a := inf_of_le_right le_top
lemma inf_top_eq (a : α) : a ⊓ ⊤ = a := inf_of_le_left le_top
@[simp]
theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  @sup_eq_bot_iff αᵒᵈ _ _ _ _
end SemilatticeInfTop
section SemilatticeInfBot
variable [SemilatticeInf α] [OrderBot α]
lemma bot_inf_eq (a : α) : ⊥ ⊓ a = ⊥ := inf_of_le_left bot_le
lemma inf_bot_eq (a : α) : a ⊓ ⊥ = ⊥ := inf_of_le_right bot_le
end SemilatticeInfBot
section Logic
section SemilatticeSup
variable [SemilatticeSup α]
theorem exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩
lemma exists_and_iff_of_monotone {P Q : α → Prop} (hP : Monotone P) (hQ : Monotone Q) :
    ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩
end SemilatticeSup
section SemilatticeInf
variable [SemilatticeInf α]
theorem exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists <| hP.dual_left
lemma exists_and_iff_of_antitone {P Q : α → Prop} (hP : Antitone P) (hQ : Antitone Q) :
    ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩
end SemilatticeInf
end Logic
section LinearOrder
variable [LinearOrder α]
theorem min_bot_left [OrderBot α] (a : α) : min ⊥ a = ⊥ := bot_inf_eq _
theorem max_top_left [OrderTop α] (a : α) : max ⊤ a = ⊤ := top_sup_eq _
theorem min_top_left [OrderTop α] (a : α) : min ⊤ a = a := top_inf_eq _
theorem max_bot_left [OrderBot α] (a : α) : max ⊥ a = a := bot_sup_eq _
theorem min_top_right [OrderTop α] (a : α) : min a ⊤ = a := inf_top_eq _
theorem max_bot_right [OrderBot α] (a : α) : max a ⊥ = a := sup_bot_eq _
theorem min_bot_right [OrderBot α] (a : α) : min a ⊥ = ⊥ := inf_bot_eq _
theorem max_top_right [OrderTop α] (a : α) : max a ⊤ = ⊤ := sup_top_eq _
theorem max_eq_bot [OrderBot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ :=
  sup_eq_bot_iff
theorem min_eq_top [OrderTop α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  inf_eq_top_iff
@[simp]
theorem min_eq_bot [OrderBot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp_rw [← le_bot_iff, inf_le_iff]
@[simp]
theorem max_eq_top [OrderTop α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  @min_eq_bot αᵒᵈ _ _ a b
end LinearOrder