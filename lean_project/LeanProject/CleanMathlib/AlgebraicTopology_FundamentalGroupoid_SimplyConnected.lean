import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
universe u
noncomputable section
open CategoryTheory
open ContinuousMap
open scoped ContinuousMap
@[mk_iff simply_connected_def]
class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)
theorem simply_connected_iff_unique_homotopic (X : Type*) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔
      Nonempty X ∧ ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
  simp only [simply_connected_def, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩
namespace SimplyConnectedSpace
variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
instance (x y : X) : Subsingleton (Path.Homotopic.Quotient x y) :=
  @Unique.instSubsingleton _ (Nonempty.some (by
    rw [simply_connected_iff_unique_homotopic] at *; tauto))
attribute [local instance] Path.Homotopic.setoid
instance (priority := 100) : PathConnectedSpace X :=
  let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp inferInstance
  { nonempty := unique_homotopic.1
    joined := fun x y => ⟨(unique_homotopic.2 x y).some.default.out⟩ }
theorem paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂ :=
  Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)
instance (priority := 100) ofContractible (Y : Type u) [TopologicalSpace Y] [ContractibleSpace Y] :
    SimplyConnectedSpace Y where
  equiv_unit :=
    let H : TopCat.of Y ≃ₕ TopCat.of PUnit.{u+1} := (ContractibleSpace.hequiv Y PUnit.{u+1}).some
    ⟨(FundamentalGroupoidFunctor.equivOfHomotopyEquiv H).trans
      FundamentalGroupoid.punitEquivDiscretePUnit⟩
end SimplyConnectedSpace
attribute [local instance] Path.Homotopic.setoid
theorem simply_connected_iff_paths_homotopic {Y : Type*} [TopologicalSpace Y] :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y) :=
  ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩
theorem simply_connected_iff_paths_homotopic' {Y : Type*} [TopologicalSpace Y] :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ := by
  convert simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl