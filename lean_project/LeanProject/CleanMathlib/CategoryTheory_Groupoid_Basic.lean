import Mathlib.CategoryTheory.Groupoid
import Mathlib.Combinatorics.Quiver.Basic
namespace CategoryTheory
namespace Groupoid
variable (C : Type*) [Groupoid C]
section Thin
theorem isThin_iff : Quiver.IsThin C ↔ ∀ c : C, Subsingleton (c ⟶ c) := by
  refine ⟨fun h c => h c c, fun h c d => Subsingleton.intro fun f g => ?_⟩
  haveI := h d
  calc
    f = f ≫ inv g ≫ g := by simp only [inv_eq_inv, IsIso.inv_hom_id, Category.comp_id]
    _ = f ≫ inv f ≫ g := by congr 1
                            simp only [inv_eq_inv, IsIso.inv_hom_id, eq_iff_true_of_subsingleton]
    _ = g := by simp only [inv_eq_inv, IsIso.hom_inv_id_assoc]
end Thin
section Disconnected
def IsTotallyDisconnected :=
  ∀ c d : C, (c ⟶ d) → c = d
end Disconnected
end Groupoid
end CategoryTheory