import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
universe v u u'
open CategoryTheory
open CategoryTheory.Limits
open LinearMap
open ModuleCat
open scoped Module
theorem IsProjective.iff_projective {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P] : Module.Projective R P ↔ Projective (ModuleCat.of R P) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · letI : Module.Projective R (ModuleCat.of R P) := h
    exact ⟨fun E X epi => Module.projective_lifting_property _ _
      ((ModuleCat.epi_iff_surjective _).mp epi)⟩
  · refine Module.Projective.of_lifting_property.{u,v} ?_
    intro E X mE mX sE sX f g s
    haveI : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
    letI : Projective (ModuleCat.of R P) := h
    exact ⟨Projective.factorThru (↟g) (↟f), Projective.factorThru_comp (↟g) (↟f)⟩
namespace ModuleCat
variable {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}
theorem projective_of_free {ι : Type u'} (b : Basis ι R M) : Projective M :=
  Projective.of_iso (ModuleCat.ofSelfIso M)
    (IsProjective.iff_projective.{v,u}.mp (Module.Projective.of_basis b))
instance moduleCat_enoughProjectives : EnoughProjectives (ModuleCat.{max u v} R) where
  presentation M :=
    ⟨{  p := ModuleCat.of R (M →₀ R)
        projective :=
          projective_of_free.{v,u} (ι := M) (M := ModuleCat.of R (M →₀ R)) <|
            Finsupp.basisSingleOne
        f := Finsupp.basisSingleOne.constr ℕ _root_.id
        epi := (epi_iff_range_eq_top _).mpr
            (range_eq_top.2 fun m => ⟨Finsupp.single m (1 : R), by
              dsimp [Basis.constr]
              simp only [Finsupp.lmapDomain_id, comp_id]
              erw [Finsupp.linearCombination_single]
              rw [one_smul]
              rfl ⟩) }⟩
end ModuleCat