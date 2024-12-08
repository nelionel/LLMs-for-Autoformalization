import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.LeftExact
universe v₁ u₁
noncomputable section
open CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type v₁} [SmallCategory C] {D : Type v₁} [SmallCategory D] (G : C ⥤ D)
variable (A : Type u₁) [Category.{v₁} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]
variable [PreservesFilteredColimits (forget A)] [(forget A).ReflectsIsomorphisms]
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms
instance {X : C} : IsCofiltered (J.Cover X) :=
  inferInstance
@[simps!]
def Functor.sheafPullback : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A
instance [RepresentablyFlat G] : PreservesFiniteLimits (G.sheafPullback A J K) := by
  have : PreservesFiniteLimits (G.op.lan ⋙ presheafToSheaf K A) :=
    comp_preservesFiniteLimits _ _
  apply comp_preservesFiniteLimits
def Functor.sheafAdjunctionContinuous [Functor.IsContinuous.{v₁} G J K] :
    G.sheafPullback A J K ⊣ G.sheafPushforwardContinuous A J K :=
  ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
end CategoryTheory