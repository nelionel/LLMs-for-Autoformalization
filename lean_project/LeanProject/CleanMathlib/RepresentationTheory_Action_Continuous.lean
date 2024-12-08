import Mathlib.RepresentationTheory.Action.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Category.TopCat.Basic
universe u v
open CategoryTheory Limits
variable (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V] [HasForget₂ V TopCat]
variable (G : MonCat.{u}) [TopologicalSpace G]
namespace Action
instance : HasForget₂ (Action V G) TopCat :=
  HasForget₂.trans (Action V G) V TopCat
instance (X : Action V G) : MulAction G ((CategoryTheory.forget₂ _ TopCat).obj X) where
  smul g x := ((CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
  one_smul x := by
    show ((CategoryTheory.forget₂ _ TopCat).map (X.ρ 1)) x = x
    simp
  mul_smul g h x := by
    show (CategoryTheory.forget₂ _ TopCat).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget₂ _ TopCat).map (X.ρ h) ≫
        (CategoryTheory.forget₂ _ TopCat).map (X.ρ g)) x
    rw [← Functor.map_comp, map_mul]
    rfl
variable {V G}
abbrev IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)
end Action
open Action
def ContAction : Type _ := FullSubcategory (IsContinuous (V := V) (G := G))
namespace ContAction
instance : Category (ContAction V G) :=
  FullSubcategory.category (IsContinuous (V := V) (G := G))
instance : ConcreteCategory (ContAction V G) :=
  FullSubcategory.concreteCategory (IsContinuous (V := V) (G := G))
instance : HasForget₂ (ContAction V G) (Action V G) :=
  FullSubcategory.hasForget₂ (IsContinuous (V := V) (G := G))
instance : HasForget₂ (ContAction V G) V :=
  HasForget₂.trans (ContAction V G) (Action V G) V
instance : HasForget₂ (ContAction V G) TopCat :=
  HasForget₂.trans (ContAction V G) (Action V G) TopCat
instance : Coe (ContAction V G) (Action V G) where
  coe X := X.obj
variable {V G}
abbrev IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)
end ContAction
open ContAction
def DiscreteContAction : Type _ := FullSubcategory (IsDiscrete (V := V) (G := G))
namespace DiscreteContAction
instance : Category (DiscreteContAction V G) :=
  FullSubcategory.category (IsDiscrete (V := V) (G := G))
instance : ConcreteCategory (DiscreteContAction V G) :=
  FullSubcategory.concreteCategory (IsDiscrete (V := V) (G := G))
instance : HasForget₂ (DiscreteContAction V G) (ContAction V G) :=
  FullSubcategory.hasForget₂ (IsDiscrete (V := V) (G := G))
instance : HasForget₂ (DiscreteContAction V G) TopCat :=
  HasForget₂.trans (DiscreteContAction V G) (ContAction V G) TopCat
variable {V G}
instance (X : DiscreteContAction V G) :
    DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X) :=
  X.property
end DiscreteContAction