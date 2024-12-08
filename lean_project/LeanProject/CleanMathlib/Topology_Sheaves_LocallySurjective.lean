import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective
universe v u
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike
noncomputable section
open CategoryTheory
open TopologicalSpace
open Opposite
namespace TopCat.Presheaf
section LocallySurjective
open scoped AlgebraicGeometry
variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {X : TopCat.{v}}
variable {ℱ 𝒢 : X.Presheaf C}
def IsLocallySurjective (T : ℱ ⟶ 𝒢) :=
  CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) T
theorem isLocallySurjective_iff (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔
      ∀ (U t), ∀ x ∈ U, ∃ (V : _) (ι : V ⟶ U), (∃ s, T.app _ s = t |_ₕ ι) ∧ x ∈ V :=
  ⟨fun h _ => h.imageSieve_mem, fun h => ⟨h _⟩⟩
section SurjectiveOnStalks
variable [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]
theorem locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔ ∀ x : X, Function.Surjective ((stalkFunctor C x).map T) := by
  constructor <;> intro hT
  · 
    intro x g
    obtain ⟨U, hxU, t, rfl⟩ := 𝒢.germ_exist x g
    rcases hT.imageSieve_mem t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩
    use ℱ.germ _ x hxV s
    convert stalkFunctor_map_germ_apply V x hxV T s using 1
    simpa [h_eq] using (germ_res_apply 𝒢 ι x hxV t).symm
  · 
    constructor
    intro U t x hxU
    set t_x := 𝒢.germ _ x hxU t with ht_x
    obtain ⟨s_x, hs_x : ((stalkFunctor C x).map T) s_x = t_x⟩ := hT x t_x
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.germ_exist x s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T.app _ s) t <| by
      convert hs_x using 1
      symm
      convert stalkFunctor_map_germ_apply _ _ _ _ s
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
    refine ⟨W, hWU, ⟨ℱ.map hWV.op s, ?_⟩, hxW⟩
    convert h_eq using 1
    simp only [← comp_apply, T.naturality]
end SurjectiveOnStalks
end LocallySurjective
end TopCat.Presheaf