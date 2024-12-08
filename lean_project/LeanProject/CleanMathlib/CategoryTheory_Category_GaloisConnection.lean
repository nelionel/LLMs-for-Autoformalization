import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.GaloisConnection
universe u v
section
variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => CategoryTheory.homOfLE (gc.le_u f.le)
          invFun := fun f => CategoryTheory.homOfLE (gc.l_le f.le)
          left_inv := by aesop_cat
          right_inv := by aesop_cat } }
end
namespace CategoryTheory
variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩
end CategoryTheory