import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Logic.Small.Set
namespace CategoryTheory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
namespace StructuredArrow
variable {S : D} {T : C ⥤ D}
instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
end StructuredArrow
namespace CostructuredArrow
variable {S : C ⥤ D} {T : D}
instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
end CostructuredArrow
end CategoryTheory