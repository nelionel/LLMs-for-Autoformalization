import Mathlib.Data.Set.Operations
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Set
import Mathlib.Util.AssertExists
assert_not_exists Finset
assert_not_exists MonoidWithZero
assert_not_exists OrderedRing
universe u v
open Function
variable {α β : Sort*}
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _
theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩
theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h
theorem Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β :=
  let ⟨e⟩ := h; ⟨f.symm.trans e⟩
theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩
theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff
theorem Finite.ofBijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›
instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm
instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm
class Infinite (α : Sort*) : Prop where
  not_finite : ¬Finite α
@[simp]
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩
@[simp]
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm
theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
  not_finite_iff_infinite.symm.trans <| e.finite_iff.not.trans not_finite_iff_infinite
instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›
instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›
theorem finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 not_finite_iff_infinite.1
theorem not_finite (α : Sort*) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›
protected theorem Finite.false [Infinite α] (_ : Finite α) : False :=
  not_finite α
protected theorem Infinite.false [Finite α] (_ : Infinite α) : False :=
  @Infinite.not_finite α ‹_› ‹_›
alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite
instance Bool.instFinite : Finite Bool := .intro finTwoEquiv.symm
instance Prop.instFinite : Finite Prop := .of_equiv _ Equiv.propEquivBool.symm
section Set
open Set Function
variable {α : Type u} {β : Type v}
namespace Set
protected def Finite (s : Set α) : Prop := Finite s
end Set
namespace Set
theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := .rfl
theorem toFinite (s : Set α) [Finite s] : s.Finite := ‹_›
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s := h
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite
@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not
alias ⟨_, Finite.not_infinite⟩ := not_infinite
attribute [simp] Finite.not_infinite
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _
protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _
end Set
theorem Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.Finite := by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]
namespace Set
variable {s t : Set α}
theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.not
alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff
end Set
end Set