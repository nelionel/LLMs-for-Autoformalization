import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
universe u
open CategoryTheory
open TopCat
namespace TopCat
@[simps! unit counit]
def adj₁ : discrete ⊣ forget TopCat.{u} where
  unit := { app := fun _ => id }
  counit := { app := fun _ => ⟨id, continuous_bot⟩ }
@[simps! unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial where
  unit := { app := fun _ => ⟨id, continuous_top⟩ }
  counit := { app := fun _ => id }
instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩
instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩
end TopCat