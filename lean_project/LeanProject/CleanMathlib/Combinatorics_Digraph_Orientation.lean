import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
variable {V : Type*}
namespace Digraph
section toSimpleGraph
def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj
def toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ G.Adj v w ∧ G.Adj w v
  symm _ _ h := And.intro h.1.symm h.2.symm
  loopless _ h := h.1 rfl
lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) :
    G.toSimpleGraphStrict ≤ G.toSimpleGraphInclusive :=
  fun _ _ h ↦ ⟨h.1, Or.inl h.2.1⟩
@[mono]
lemma toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ → SimpleGraph V) := by
  intro _ _ h₁ _ _ h₂
  apply And.intro h₂.1
  cases h₂.2
  · exact Or.inl <| h₁ ‹_›
  · exact Or.inr <| h₁ ‹_›
@[mono]
lemma toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ And.intro h₂.1 <| And.intro (h₁ h₂.2.1) (h₁ h₂.2.2)
@[simp]
lemma toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, Or.inl trivial⟩⟩
@[simp]
lemma toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, trivial, trivial⟩⟩
@[simp]
lemma toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩
@[simp]
lemma toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩
end toSimpleGraph
end Digraph