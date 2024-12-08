import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Atoms
import Mathlib.Order.Minimal
open Finset
namespace Fintype
variable {ι α : Type*} [Fintype ι] [Fintype α]
section Nonempty
variable (α) [Nonempty α]
abbrev toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le a := inf'_le _ <| mem_univ a
abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  le_top a := le_sup' id <| mem_univ a
abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }
end Nonempty
section BoundedOrder
variable (α)
open scoped Classical
noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  le_sSup := fun _ _ ha => Finset.le_sup (f := id) (Set.mem_toFinset.mpr ha)
  sSup_le := fun _ _ ha => Finset.sup_le fun _ hb => ha _ <| Set.mem_toFinset.mp hb
  sInf_le := fun _ _ ha => Finset.inf_le (Set.mem_toFinset.mpr ha)
  le_sInf := fun _ _ ha => Finset.le_inf fun _ hb => ha _ <| Set.mem_toFinset.mp hb
noncomputable abbrev toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice.MinimalAxioms α where
  __ := toCompleteLattice α
  iInf_sup_le_sup_sInf := fun a s => by
    convert (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl
noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α := .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)
noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra with }
noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α
noncomputable abbrev toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra
end BoundedOrder
section Nonempty
variable (α) [Nonempty α]
noncomputable abbrev toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| @toBoundedOrder α _ ⟨Classical.arbitrary α⟩ _
noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α := by
  let _ := toBoundedOrder α
  exact { toCompleteLatticeOfNonempty α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra with }
end Nonempty
end Fintype
section PartialOrder
variable {α : Type*} [PartialOrder α] {a : α} {p : α → Prop}
lemma Finite.exists_minimal_le [Finite α] (h : p a) : ∃ b, b ≤ a ∧ Minimal p b := by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    Set.Finite.exists_minimal_wrt id {x | x ≤ a ∧ p x} (Set.toFinite _) ⟨a, rfl.le, h⟩
  exact ⟨b, hba, hb, fun x hx hxb ↦ (hbmin x ⟨hxb.trans hba, hx⟩ hxb).le⟩
@[deprecated (since := "2024-09-23")] alias Finite.exists_ge_minimal := Finite.exists_minimal_le
lemma Finite.exists_le_maximal [Finite α] (h : p a) : ∃ b, a ≤ b ∧ Maximal p b :=
  Finite.exists_minimal_le (α := αᵒᵈ) h
lemma Finset.exists_minimal_le (s : Finset α) (h : a ∈ s) : ∃ b, b ≤ a ∧ Minimal (· ∈ s) b := by
  obtain ⟨⟨b, _⟩, lb, minb⟩ := @Finite.exists_minimal_le s _ ⟨a, h⟩ (·.1 ∈ s) _ h
  use b, lb; rwa [minimal_subtype, inf_idem] at minb
lemma Finset.exists_le_maximal (s : Finset α) (h : a ∈ s) : ∃ b, a ≤ b ∧ Maximal (· ∈ s) b :=
  s.exists_minimal_le (α := αᵒᵈ) h
lemma Set.Finite.exists_minimal_le {s : Set α} (hs : s.Finite) (h : a ∈ s) :
    ∃ b, b ≤ a ∧ Minimal (· ∈ s) b := by
  obtain ⟨b, lb, minb⟩ := hs.toFinset.exists_minimal_le (hs.mem_toFinset.mpr h)
  use b, lb; simpa using minb
lemma Set.Finite.exists_le_maximal {s : Set α} (hs : s.Finite) (h : a ∈ s) :
    ∃ b, a ≤ b ∧ Maximal (· ∈ s) b :=
  hs.exists_minimal_le (α := αᵒᵈ) h
end PartialOrder
noncomputable instance Fin.completeLinearOrder {n : ℕ} [NeZero n] : CompleteLinearOrder (Fin n) :=
  Fintype.toCompleteLinearOrder _
noncomputable instance Bool.completeLinearOrder : CompleteLinearOrder Bool :=
  Fintype.toCompleteLinearOrder _
noncomputable instance Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _
noncomputable instance Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool :=
  Fintype.toCompleteAtomicBooleanAlgebra _
variable {α : Type*} {r : α → α → Prop} [IsTrans α r] {β γ : Type*} [Nonempty γ] {f : γ → α}
  [Finite β]
theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]
theorem Directed.finite_le (D : Directed r f) (g : β → γ) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  classical
    obtain ⟨z, hz⟩ := D.finite_set_le (Set.finite_range g)
    exact ⟨z, fun i => hz (g i) ⟨i, rfl⟩⟩
variable [Nonempty α] [Preorder α]
theorem Finite.exists_le [IsDirected α (· ≤ ·)] (f : β → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.finite_le _
theorem Finite.exists_ge [IsDirected α (· ≥ ·)] (f : β → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.finite_le (r := (· ≥ ·)) _
theorem Set.Finite.exists_le [IsDirected α (· ≤ ·)] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finite_set_le hs
theorem Set.Finite.exists_ge [IsDirected α (· ≥ ·)] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, M ≤ i :=
  directed_id.finite_set_le (r := (· ≥ ·)) hs
@[simp]
theorem Finite.bddAbove_range [IsDirected α (· ≤ ·)] (f : β → α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b
@[simp]
theorem Finite.bddBelow_range [IsDirected α (· ≥ ·)] (f : β → α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b