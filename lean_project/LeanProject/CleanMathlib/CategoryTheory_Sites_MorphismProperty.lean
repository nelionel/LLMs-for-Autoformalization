import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Pretopology
namespace CategoryTheory
open Limits
variable {C : Type*} [Category C] [HasPullbacks C]
namespace MorphismProperty
def pretopology (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    Pretopology C where
  coverings X S := ∀ {Y : C} {f : Y ⟶ X}, S f → P f
  has_isos X Y f h Z g hg := by
    cases hg
    exact P.of_isIso f
  pullbacks X Y f S hS Z g hg := by
    obtain ⟨Z, g, hg⟩ := hg
    apply P.pullback_snd g f (hS hg)
  transitive X S Ti hS hTi Y f hf := by
    obtain ⟨Z, g, h, H, H', rfl⟩ := hf
    exact comp_mem _ _ _ (hTi h H H') (hS H)
abbrev grothendieckTopology (P : MorphismProperty C) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : GrothendieckTopology C :=
  P.pretopology.toGrothendieck
variable {P Q : MorphismProperty C}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
lemma pretopology_le (hPQ : P ≤ Q) : P.pretopology ≤ Q.pretopology :=
  fun _ _ hS _ f hf ↦ hPQ f (hS hf)
variable (P Q) in
lemma pretopology_inf :
    (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology := by
  ext X S
  exact ⟨fun hS ↦ ⟨fun hf ↦ (hS hf).left, fun hf ↦ (hS hf).right⟩,
    fun h ↦ fun hf ↦ ⟨h.left hf, h.right hf⟩⟩
end CategoryTheory.MorphismProperty