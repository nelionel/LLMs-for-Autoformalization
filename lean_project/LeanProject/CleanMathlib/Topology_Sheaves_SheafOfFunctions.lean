import Mathlib.Topology.Sheaves.PresheafOfFunctions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
open CategoryTheory Limits TopologicalSpace Opens
universe u
noncomputable section
variable (X : TopCat.{u})
open TopCat
namespace TopCat.Presheaf
theorem toTypes_isSheaf (T : X → Type u) : (presheafToTypes X T).IsSheaf :=
  isSheaf_of_isSheafUniqueGluing_types.{u} _ fun ι U sf hsf => by
    choose index index_spec using fun x : ↑(iSup U) => Opens.mem_iSup.mp x.2
    let s : ∀ x : ↑(iSup U), T x := fun x => sf (index x) ⟨x.1, index_spec x⟩
    refine ⟨s, ?_, ?_⟩
    · intro i
      funext x
      exact congr_fun (hsf (index ⟨x, _⟩) i) ⟨x, ⟨index_spec ⟨x.1, _⟩, x.2⟩⟩
    · 
      intro t ht
      funext x
      exact congr_fun (ht (index x)) ⟨x.1, index_spec x⟩
theorem toType_isSheaf (T : Type u) : (presheafToType X T).IsSheaf :=
  toTypes_isSheaf X fun _ => T
end TopCat.Presheaf
namespace TopCat
def sheafToTypes (T : X → Type u) : Sheaf (Type u) X :=
  ⟨presheafToTypes X T, Presheaf.toTypes_isSheaf _ _⟩
def sheafToType (T : Type u) : Sheaf (Type u) X :=
  ⟨presheafToType X T, Presheaf.toType_isSheaf _ _⟩
end TopCat