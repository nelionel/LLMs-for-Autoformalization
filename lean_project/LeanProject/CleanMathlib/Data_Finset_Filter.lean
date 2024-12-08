import Mathlib.Data.Finset.Empty
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset
assert_not_exists CompleteLattice
assert_not_exists OrderedCommMonoid
open Multiset Subtype Function
universe u
variable {α : Type*} {β : Type*} {γ : Type*}
namespace Finset
attribute [local trans] Subset.trans Superset.trans
section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
end Finset.Filter
namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder
def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=
  match expectedType? with
  | some expectedType =>
    match_expr expectedType with
    | Finset _ => pure true
    | Set _ => throwUnsupportedSyntax
    | _ => pure false
  | none => pure false
@[term_elab setBuilder]
def elabFinsetBuilderSep : TermElab
  | `({ $x:ident ∈ $s:term | $p }), expectedType? => do
    unless ← knownToBeFinsetNotSet expectedType? do
      let ty ← try whnfR (← inferType (← elabTerm s none)) catch _ => throwUnsupportedSyntax
      match_expr ty with
      | Finset _ => pure ()
      | _ => throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) $s)) expectedType?
  | _, _ => throwUnsupportedSyntax
end Mathlib.Meta
namespace Finset
section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}
@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl
@[simp]
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  Multiset.filter_subset _ _
variable {p}
@[simp]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Multiset.mem_filter
theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
  Multiset.mem_of_mem_filter h
theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x :=
  ⟨fun h =>
    let ⟨x, hs, hp⟩ := Set.exists_of_ssubset h
    ⟨x, hs, mt (fun hp => mem_filter.2 ⟨hs, hp⟩) hp⟩,
    fun ⟨_, hs, hp⟩ => ⟨s.filter_subset _, fun h => hp (mem_filter.1 (h hs)).2⟩⟩
variable (p)
theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a :=
  ext fun a => by
    simp only [mem_filter, and_assoc, Bool.decide_and, Bool.decide_coe, Bool.and_eq_true]
theorem filter_comm (s : Finset α) : (s.filter p).filter q = (s.filter q).filter p := by
  simp_rw [filter_filter, and_comm]
theorem filter_congr_decidable (s : Finset α) (p : α → Prop) (h : DecidablePred p)
    [DecidablePred p] : @filter α p h s = s.filter p := by congr
@[simp]
theorem filter_True {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp
@[simp]
theorem filter_False {h} (s : Finset α) : @filter _ (fun _ => False) h s = ∅ := by ext; simp
variable {p q}
lemma filter_eq_self : s.filter p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]
theorem filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬p x := by simp [Finset.ext_iff]
theorem filter_nonempty_iff : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]
theorem filter_true_of_mem (h : ∀ x ∈ s, p x) : s.filter p = s := filter_eq_self.2 h
theorem filter_false_of_mem (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h
@[simp]
theorem filter_const (p : Prop) [Decidable p] (s : Finset α) :
    (s.filter fun _a => p) = if p then s else ∅ := by split_ifs <;> simp [*]
theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| Multiset.filter_congr H
variable (p q)
@[simp]
theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _
@[gcongr]
theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p
@[gcongr]
theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : s.filter p ⊆ s.filter q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)
@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter
theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩
theorem disjoint_filter_filter {s t : Finset α}
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)
lemma _root_.Set.pairwiseDisjoint_filter [DecidableEq β] (f : α → β) (s : Set β) (t : Finset α) :
    s.PairwiseDisjoint fun x ↦ t.filter (f · = x) := by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = j := by simpa using hj hx
  contradiction
variable {p q}
lemma filter_inj : s.filter p = t.filter p ↔ ∀ ⦃a⦄, p a → (a ∈ s ↔ a ∈ t) := by
  simp [Finset.ext_iff]
lemma filter_inj' : s.filter p = s.filter q ↔ ∀ ⦃a⦄, a ∈ s → (p a ↔ q a) := by
  simp [Finset.ext_iff]
end Filter
end Finset