import Mathlib.Combinatorics.Hall.Finite
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.Rel
open Finset Function CategoryTheory
universe u v
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f : ι' → α | Function.Injective f ∧ ∀ (x : {x // x ∈ ι'}), f x ∈ t x }
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' := by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  cases' f.property with hinj hc
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) :
    (Finset ι)ᵒᵖ ⥤ Type max u v where
  obj ι' := hallMatchingsOn t ι'.unop
  map {_ _} g f := hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop) f
instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' → ι' → ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  · intro h
    haveI : ∀ ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      haveI : ∀ ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      refine ⟨?_, ?_, ?_⟩
      ·
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [Opposite.unop_op, mem_singleton]⟩
      · 
        intro i i'
        have subi : ({i} : Finset ι) ⊆ {i, i'} := by simp
        have subi' : ({i'} : Finset ι) ⊆ {i, i'} := by simp
        rw [← Finset.le_iff_subset] at subi subi'
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op, ← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · 
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · 
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    intro
    rw [Finset.mem_image, Finset.mem_biUnion]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf₂ x⟩
instance {α : Type u} {β : Type v} [DecidableEq β] (r : α → β → Prop)
    [∀ a : α, Fintype (Rel.image r {a})] (A : Finset α) : Fintype (Rel.image r A) := by
  have h : Rel.image r A = (A.biUnion fun a => (Rel.image r {a}).toFinset : Set β) := by
    ext
    simp [Rel.image, (Set.mem_toFinset)]
  rw [h]
  apply FinsetCoe.fintype
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (r : α → β → Prop) [∀ a : α, Fintype (Rel.image r {a})] :
    (∀ A : Finset α, #A ≤ Fintype.card (Rel.image r A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, r x (f x) := by
  let r' a := (Rel.image r {a}).toFinset
  have h : ∀ A : Finset α, Fintype.card (Rel.image r A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [Rel.image, (Set.mem_toFinset)]
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [Rel.image, (Set.mem_toFinset)]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [∀ a, DecidablePred (r a)] :
    (∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) ↔ ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) := by
  haveI := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : ∀ A : Finset α, ({b | ∃ a ∈ A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective