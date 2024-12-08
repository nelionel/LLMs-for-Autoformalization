import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
open CategoryTheory Limits
open CategoryTheory
universe u v w
def Condensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology CompHaus.{u}) C
instance {C : Type w} [Category.{v} C] : Category (Condensed.{u} C) :=
  show Category (Sheaf _ _) from inferInstance
abbrev CondensedSet := Condensed.{u} (Type (u+1))
namespace Condensed
variable {C : Type w} [Category.{v} C]
@[simp]
lemma id_val (X : Condensed.{u} C) : (𝟙 X : X ⟶ X).val = 𝟙 _ := rfl
@[simp]
lemma comp_val {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl
@[ext]
lemma hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.val.app S = g.val.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _
end Condensed
namespace CondensedSet
@[simp]
lemma hom_naturality_apply {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x
end CondensedSet