import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
universe u
open CategoryTheory Limits Topology
namespace TopCat
noncomputable
def effectiveEpiStructOfQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) (hπ : IsQuotientMap π) :
    EffectiveEpiStruct π where
  desc e h := hπ.lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := (hπ.lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = hπ.liftEquiv ⟨e,
      fun a b hab ↦ DFunLike.congr_fun
        (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩ (by ext; exact hab))
        a⟩ by assumption
    rw [← Equiv.symm_apply_eq hπ.liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl
theorem effectiveEpi_iff_isQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) :
    EffectiveEpi π ↔ IsQuotientMap π := by
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiStructOfQuotientMap π hπ⟩⟩⟩
  have hπ : RegularEpi π := inferInstance
  let F := parallelPair hπ.left hπ.right
  let i : B ≅ colimit F := hπ.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  suffices IsQuotientMap (homeoOfIso i ∘ π) by
    simpa [← Function.comp_assoc] using (homeoOfIso i).symm.isQuotientMap.comp this
  constructor
  · change Function.Surjective (π ≫ i.hom)
    rw [← epi_iff_surjective]
    infer_instance
  · ext U
    have : π ≫ i.hom = colimit.ι F WalkingParallelPair.one := by simp [i, ← Iso.eq_comp_inv]
    rw [isOpen_coinduced (f := (homeoOfIso i ∘ π)), coequalizer_isOpen_iff _ U, ← this]
    rfl
@[deprecated (since := "2024-10-22")]
alias effectiveEpi_iff_quotientMap := effectiveEpi_iff_isQuotientMap
end TopCat