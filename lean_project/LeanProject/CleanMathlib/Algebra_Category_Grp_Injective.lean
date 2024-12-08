import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Instances.AddCircle
open CategoryTheory
open Pointwise
universe u
variable (A : Type u) [AddCommGroup A]
theorem Module.Baer.of_divisible [DivisibleBy A ℤ] : Module.Baer ℤ A := fun I g ↦ by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn ↦ ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gₘ m), fun n hn ↦ ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gₘ h0, ← map_zsmul g,
    SetLike.mk_smul_mk]
namespace AddCommGrp
theorem injective_as_module_iff : Injective (⟨A⟩ : ModuleCat ℤ) ↔
    Injective (⟨A,inferInstance⟩ : AddCommGrp) :=
  ((forget₂ (ModuleCat ℤ) AddCommGrp).asEquivalence.map_injective_iff ⟨A⟩).symm
instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (⟨A,inferInstance⟩ : AddCommGrp) :=
  (injective_as_module_iff A).mp <|
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)
instance injective_ratCircle : Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  injective_of_divisible _
end AddCommGrp