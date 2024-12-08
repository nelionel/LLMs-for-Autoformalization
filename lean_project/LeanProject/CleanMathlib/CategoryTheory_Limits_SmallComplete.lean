import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.SetTheory.Cardinal.Basic
namespace CategoryTheory
open Category Limits
open Cardinal
universe u
variable {C : Type u} [SmallCategory C] [HasProducts.{u} C]
instance (priority := 100) : Quiver.IsThin C := fun X Y =>
  ⟨fun r s => by
    classical
      by_contra r_ne_s
      have z : (2 : Cardinal) ≤ #(X ⟶ Y) := by
        rw [Cardinal.two_le_iff]
        exact ⟨_, _, r_ne_s⟩
      let md := ΣZ W : C, Z ⟶ W
      let α := #md
      apply not_le_of_lt (Cardinal.cantor α)
      let yp : C := ∏ᶜ fun _ : md => Y
      apply _root_.trans _ _
      · exact #(X ⟶ yp)
      · apply le_trans (Cardinal.power_le_power_right z)
        rw [Cardinal.power_def]
        apply le_of_eq
        rw [Cardinal.eq]
        refine ⟨⟨Pi.lift, fun f k => f ≫ Pi.π _ k, ?_, ?_⟩⟩
        · intro f
          ext k
          simp
        · intro f
          ext ⟨j⟩
          simp
      · apply Cardinal.mk_le_of_injective _
        · intro f
          exact ⟨_, _, f⟩
        · rintro f g k
          cases k
          rfl⟩
end CategoryTheory