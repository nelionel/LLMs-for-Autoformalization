import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoversTop
universe u v' u'
open CategoryTheory Limits
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
namespace SheafOfModules
variable (M N P : SheafOfModules.{u} R)
structure GeneratingSections where
  I : Type u
  s : I → M.sections
  epi : Epi (M.freeHomEquiv.symm s) := by infer_instance
namespace GeneratingSections
attribute [instance] epi
variable {M N P}
noncomputable abbrev π (σ : M.GeneratingSections) : free σ.I ⟶ M := M.freeHomEquiv.symm σ.s
@[simps]
def ofEpi (σ : M.GeneratingSections) (p : M ⟶ N) [Epi p] :
    N.GeneratingSections where
  I := σ.I
  s i := sectionsMap p (σ.s i)
  epi := by
    rw [← freeHomEquiv_symm_comp]
    apply epi_comp
lemma opEpi_id (σ : M.GeneratingSections) :
    σ.ofEpi (𝟙 M) = σ := rfl
lemma opEpi_comp (σ : M.GeneratingSections) (p : M ⟶ N) (q : N ⟶ P) [Epi p] [Epi q] :
    σ.ofEpi (p ≫ q) = (σ.ofEpi p).ofEpi q := rfl
def equivOfIso (e : M ≅ N) :
    M.GeneratingSections ≃ N.GeneratingSections where
  toFun σ := σ.ofEpi e.hom
  invFun σ := σ.ofEpi e.inv
  left_inv σ := by
    dsimp
    simp only [← opEpi_comp, e.hom_inv_id, opEpi_id]
  right_inv σ := by
    dsimp
    simp only [← opEpi_comp, e.inv_hom_id, opEpi_id]
end GeneratingSections
variable [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrp.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrp.{u})]
structure LocalGeneratorsData where
  I : Type u'
  X : I → C
  coversTop : J.CoversTop X
  generators (i : I) : (M.over (X i)).GeneratingSections
class IsFiniteType : Prop where
  exists_localGeneratorsData :
    ∃ (σ : M.LocalGeneratorsData), ∀ (i : σ.I), Finite (σ.generators i).I
section
variable [h : M.IsFiniteType]
noncomputable def localGeneratorsDataOfIsFiniteType : M.LocalGeneratorsData :=
  h.exists_localGeneratorsData.choose
instance (i : M.localGeneratorsDataOfIsFiniteType.I) :
    Finite (M.localGeneratorsDataOfIsFiniteType.generators i).I :=
  h.exists_localGeneratorsData.choose_spec i
end
end SheafOfModules