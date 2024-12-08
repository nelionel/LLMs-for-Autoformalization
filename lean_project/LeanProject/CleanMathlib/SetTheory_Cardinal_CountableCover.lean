import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.Filter.Finite
open Set Order Filter
open scoped Cardinal
namespace Cardinal
universe u v
lemma mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  rcases lt_or_le a ℵ₀ with ha|ha
  · obtain ⟨n, rfl⟩ : ∃ (n : ℕ), a = n := lt_aleph0.1 ha
    apply mk_le_iff_forall_finset_subset_card_le.2 (fun s hs ↦ ?_)
    have A : ∀ x ∈ s, ∀ᶠ i in l, x ∈ f i := fun x hx ↦ ht x (hs hx)
    have B : ∀ᶠ i in l, ∀ x ∈ s, x ∈ f i := (s.eventually_all).2 A
    rcases B.exists with ⟨i, hi⟩
    have : ∀ i, Fintype (f i) := fun i ↦ (lt_aleph0_iff_fintype.1 ((h'f i).trans_lt ha)).some
    let u : Finset α := (f i).toFinset
    have I1 : s.card ≤ u.card := by
      have : s ⊆ u := fun x hx ↦ by simpa only [u, Set.mem_toFinset] using hi x hx
      exact Finset.card_le_card this
    have I2 : (u.card : Cardinal) ≤ n := by
      convert h'f i; simp only [u, Set.toFinset_card, mk_fintype]
    exact I1.trans (Nat.cast_le.1 I2)
  · have : t ⊆ ⋃ i, f i := by
      intro x hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ f i := (ht x hx).exists
      exact mem_iUnion_of_mem i hi
    calc #t ≤ #(⋃ i, f i) := mk_le_mk_of_subset this
      _     ≤ sum (fun i ↦ #(f i)) := mk_iUnion_le_sum_mk
      _     ≤ sum (fun _ ↦ a) := sum_le_sum _ _ h'f
      _     = #ι * a := by simp
      _     ≤ ℵ₀ * a := mul_le_mul_right' mk_le_aleph0 a
      _     = a := aleph0_mul_eq ha
lemma mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  let g : ULift.{u, v} ι → Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) ≤ Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  have : NeBot l' := map_neBot
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l') (f := g)
  · intro x hx
    simpa only [Function.comp_apply, mem_preimage, eventually_map] using ht _ hx
  · intro i
    simpa [g] using h'f i.down
lemma mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #α ≤ a := by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ ↦ ht x) h'f
lemma mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) = a) : #α = a := by
  apply le_antisymm
  · apply mk_le_of_countable_eventually_mem ht (fun i ↦ (h'f i).le)
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    rw [← (h'f i)]
    exact mk_set_le (f i)
end Cardinal