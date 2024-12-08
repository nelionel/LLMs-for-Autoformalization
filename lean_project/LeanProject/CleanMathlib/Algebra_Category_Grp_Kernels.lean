import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
namespace AddCommGrp
open AddMonoidHom CategoryTheory Limits QuotientAddGroup
universe u
variable {G H : AddCommGrp.{u}} (f : G ⟶ H)
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.ker) f.ker.subtype <| ext fun x => x.casesOn fun _ hx => hx
def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => (by exact Fork.ι s : _ →+ G).codRestrict _ fun c => mem_ker.mpr <|
      by exact DFunLike.congr_fun s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff_val.mpr <| by exact DFunLike.congr_fun h x)
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of <| H ⧸ f.range) (mk' f.range) <| ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩
def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => lift _ _ <| (range_le_ker_iff _ _).mpr <| CokernelCofork.condition s)
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
      (cancel_epi (cokernelCocone f).π).mp <| by simpa only [parallelPair_obj_one] using h)
end AddCommGrp