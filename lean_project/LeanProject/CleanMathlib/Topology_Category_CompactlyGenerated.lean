import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.CategoryTheory.Elementwise
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike
universe u w
open CategoryTheory Topology TopologicalSpace
structure CompactlyGenerated where
  toTop : TopCat.{w}
  [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]
namespace CompactlyGenerated
instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := { α := ULift (Fin 37) } }⟩
instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩
attribute [instance] is_compactly_generated
instance : Category.{w, w+1} CompactlyGenerated.{u, w} :=
  InducedCategory.category toTop
instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} :=
  InducedCategory.concreteCategory _
variable (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
def of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›
@[simps!]
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _
instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full
instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful
@[simps hom inv]
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x
@[simps]
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous
@[simps]
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
end CompactlyGenerated