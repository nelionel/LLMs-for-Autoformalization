import Mathlib.Order.CompleteLattice
import Mathlib.Order.CompactlyGenerated.Basic
namespace IsCompactlyGenerated
open CompleteLattice
variable {α : Type*} [CompleteLattice α]
structure BooleanGenerators (S : Set α) : Prop where
  isAtom : ∀ I ∈ S, IsAtom I
  finitelyAtomistic : ∀ (s : Finset α) (a : α),
      ↑s ⊆ S → IsCompactElement a → a ≤ s.sup id → ∃ t ⊆ s, a = t.sup id
namespace BooleanGenerators
variable {S : Set α}
lemma mono (hS : BooleanGenerators S) {T : Set α} (hTS : T ⊆ S) : BooleanGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  finitelyAtomistic := fun s a hs ↦ hS.finitelyAtomistic s a (le_trans hs hTS)
variable [IsCompactlyGenerated α]
lemma atomistic (hS : BooleanGenerators S) (a : α) (ha : a ≤ sSup S) : ∃ T ⊆ S, a = sSup T := by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : ∀ b : α, IsCompactElement b → b ≤ sSup S → ∃ T ⊆ S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := hb S hbS
    obtain ⟨t, ht, rfl⟩ := hS.finitelyAtomistic s b hs₁ hb hs₂
    refine ⟨t, ?_, Finset.sup_id_eq_sSup t⟩
    refine Set.Subset.trans ?_ hs₁
    simpa only [Finset.coe_subset] using ht
  choose T hT₁ hT₂ using aux
  use sSup {T c h₁ h₂ | (c ∈ C) (h₁ : IsCompactElement c) (h₂ : c ≤ sSup S)}
  constructor
  · apply _root_.sSup_le
    rintro _ ⟨c, -, h₁, h₂, rfl⟩
    apply hT₁
  · apply le_antisymm
    · apply _root_.sSup_le
      intro c hc
      rw [hT₂ c (hC _ hc) ((le_sSup hc).trans ha)]
      apply sSup_le_sSup
      apply _root_.le_sSup
      use c, hc, hC _ hc, (le_sSup hc).trans ha
    · simp only [Set.sSup_eq_sUnion, sSup_le_iff, Set.mem_sUnion, Set.mem_setOf_eq,
        forall_exists_index, and_imp]
      rintro a T b hbC hb hbS rfl haT
      apply (le_sSup haT).trans
      rw [← hT₂]
      exact le_sSup hbC
lemma isAtomistic_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    IsAtomistic α := by
  refine ⟨fun a ↦ ?_⟩
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI ↦ hS.isAtom I (hs hI)⟩
lemma mem_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
    (haS : a ≤ sSup S) : a ∈ S := by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a ≤ sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)).1
lemma sSup_inter (hS : BooleanGenerators S) {T₁ T₂ : Set α} (hT₁ : T₁ ⊆ S) (hT₂ : T₂ ⊆ S) :
    sSup (T₁ ∩ T₂) = (sSup T₁) ⊓ (sSup T₂) := by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup Set.inter_subset_left
    · apply sSup_le_sSup Set.inter_subset_right
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSup
  constructor
  · apply (hS.mono hT₁).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_left)
  · apply (hS.mono hT₂).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_right)
def distribLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    DistribLattice α where
  le_sup_inf a b c := by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union, ← sSup_union, ← hS.sSup_inter hTb hTc, ← hS.sSup_inter, ← sSup_union]
    on_goal 1 => congr 1; ext
    all_goals
      simp only [Set.union_subset_iff, Set.mem_inter_iff, Set.mem_union]
      tauto
lemma complementedLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    ComplementedLattice α := by
  let _i := hS.distribLattice_of_sSup_eq_top h
  have _i₁ := isAtomistic_of_sSup_eq_top hS h
  apply complementedLattice_of_isAtomistic
noncomputable
def booleanAlgebra_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) : BooleanAlgebra α :=
  let _i := hS.distribLattice_of_sSup_eq_top h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebraOfComplemented α
lemma sSup_le_sSup_iff_of_atoms (hS : BooleanGenerators S) (X Y : Set α) (hX : X ⊆ S) (hY : Y ⊆ S) :
    sSup X ≤ sSup Y ↔ X ⊆ Y := by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha
lemma eq_atoms_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    S = {a : α | IsAtom a} := by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)
end BooleanGenerators
end IsCompactlyGenerated