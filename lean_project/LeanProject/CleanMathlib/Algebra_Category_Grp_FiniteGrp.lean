import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Category.Grp.Basic
universe u v
open CategoryTheory
@[pp_with_univ]
structure FiniteGrp where
  toGrp : Grp
  [isFinite : Finite toGrp]
@[pp_with_univ]
structure FiniteAddGrp where
  toAddGrp : AddGrp
  [isFinite : Finite toAddGrp]
attribute [to_additive] FiniteGrp
namespace FiniteGrp
@[to_additive]
instance : CoeSort FiniteGrp.{u} (Type u) where
  coe G := G.toGrp
@[to_additive]
instance : Category FiniteGrp := InducedCategory.category FiniteGrp.toGrp
@[to_additive]
instance : ConcreteCategory FiniteGrp := InducedCategory.concreteCategory FiniteGrp.toGrp
@[to_additive]
instance (G : FiniteGrp) : Group G := inferInstanceAs <| Group G.toGrp
@[to_additive]
instance (G : FiniteGrp) : Finite G := G.isFinite
@[to_additive]
instance (G H : FiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs <| FunLike (G →* H) G H
@[to_additive]
instance (G H : FiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs <| MonoidHomClass (G →* H) G H
@[to_additive "Construct a term of `FiniteAddGrp` from a type endowed with the structure of a
finite additive group."]
def of (G : Type u) [Group G] [Finite G] : FiniteGrp where
  toGrp := Grp.of G
  isFinite := ‹_›
@[to_additive "The morphism in `FiniteAddGrp`, induced from a morphism of the category `AddGrp`"]
def ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) : of X ⟶ of Y :=
  Grp.ofHom f
@[to_additive]
lemma ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) (x : X) :
    ofHom f x = f x :=
  rfl
end FiniteGrp