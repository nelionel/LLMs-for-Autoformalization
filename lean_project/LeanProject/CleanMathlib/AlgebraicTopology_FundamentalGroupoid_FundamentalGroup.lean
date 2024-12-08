import Mathlib.CategoryTheory.Groupoid
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
universe u
variable {X : Type u} [TopologicalSpace X]
variable {x₀ x₁ : X}
noncomputable section
open CategoryTheory
def FundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) :=
  @Aut (FundamentalGroupoid X) _ ⟨x⟩
instance (X : Type u) [TopologicalSpace X] (x : X) : Group (FundamentalGroup X x) := by
  dsimp only [FundamentalGroup]
  infer_instance
instance (X : Type u) [TopologicalSpace X] (x : X) : Inhabited (FundamentalGroup X x) := by
  dsimp only [FundamentalGroup]
  infer_instance
namespace FundamentalGroup
attribute [local instance] Path.Homotopic.setoid
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  Aut.autMulEquivOfIso (asIso ⟦p⟧)
variable (x₀ x₁)
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)
abbrev toArrow {X : TopCat} {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p.hom
abbrev toPath {X : TopCat} {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p
abbrev fromArrow {X : TopCat} {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x where
  hom := p
  inv := CategoryTheory.Groupoid.inv p
abbrev fromPath {X : TopCat} {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p
end FundamentalGroup