import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.Algebra.StarSubalgebra
open scoped Pointwise ENNReal NNReal ComplexOrder
open WeakDual WeakDual.CharacterSpace
variable {A : Type*} [CStarAlgebra A]
namespace StarAlgebra.elemental
instance {R A : Type*} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elemental R a) :=
  { SubringClass.toNormedRing (elemental R a) with
    mul_comm := mul_comm }
noncomputable instance (a : A) [IsStarNormal a] : CommCStarAlgebra (elemental ℂ a) where
  mul_comm := mul_comm
variable (a : A) [IsStarNormal a]
@[simps]
noncomputable def characterSpaceToSpectrum (x : A)
    (φ : characterSpace ℂ (elemental ℂ x)) : spectrum ℂ x where
  val := φ ⟨x, self_mem ℂ x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed ℂ x)
      (a := ⟨x, self_mem ℂ x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem ℂ x⟩
@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.characterSpaceToSpectrum := characterSpaceToSpectrum
theorem continuous_characterSpaceToSpectrum (x : A) :
    Continuous (characterSpaceToSpectrum x) :=
  continuous_induced_rng.2
    (map_continuous <| gelfandTransform ℂ (elemental ℂ x) ⟨x, self_mem ℂ x⟩)
@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.continuous_characterSpaceToSpectrum :=
  continuous_characterSpaceToSpectrum
theorem bijective_characterSpaceToSpectrum :
    Function.Bijective (characterSpaceToSpectrum a) := by
  refine ⟨fun φ ψ h => starAlgHomClass_ext ℂ ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed ℂ a)
      (a := ⟨a, self_mem ℂ a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩
@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.bijective_characterSpaceToSpectrum :=
  bijective_characterSpaceToSpectrum
noncomputable def characterSpaceHomeo :
    characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)
@[deprecated (since := "2024-11-05")]
alias _root_.elementalStarAlgebra.characterSpaceHomeo := characterSpaceHomeo
end StarAlgebra.elemental
open StarAlgebra elemental
variable (a : A) [IsStarNormal a]
noncomputable def continuousFunctionalCalculus :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a :=
  ((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans
    (gelfandStarTransform (elemental ℂ a)).symm
theorem continuousFunctionalCalculus_map_id :
    continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, self_mem ℂ a⟩ :=
  (gelfandStarTransform (elemental ℂ a)).symm_apply_apply _