import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
universe u v' u'
open CategoryTheory Limits
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
namespace SheafOfModules
variable (M : SheafOfModules.{u} R)
section
variable [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
structure Presentation where
  generators : M.GeneratingSections
  relations : (kernel generators.π).GeneratingSections
end
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrp.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrp.{u}]
structure QuasicoherentData where
  I : Type u'
  X : I → C
  coversTop : J.CoversTop X
  presentation (i : I) : (M.over (X i)).Presentation
namespace QuasicoherentData
variable {M}
@[simps]
def localGeneratorsData (q : M.QuasicoherentData) : M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators
end QuasicoherentData
class IsQuasicoherent : Prop where
  nonempty_quasicoherentData : Nonempty M.QuasicoherentData
class IsFinitePresentation : Prop where
  exists_quasicoherentData :
    ∃ (σ : M.QuasicoherentData), ∀ (i : σ.I), (Finite (σ.presentation i).generators.I ∧
      Finite (σ.presentation i).relations.I)
section
variable [h : M.IsFinitePresentation]
noncomputable def quasicoherentDataOfIsFinitePresentation : M.QuasicoherentData :=
  h.exists_quasicoherentData.choose
instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).generators.I :=
  have : _ ∧ Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
    h.exists_quasicoherentData.choose_spec i
  this.1
instance (i : M.quasicoherentDataOfIsFinitePresentation.I) :
    Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
  have : _ ∧ Finite (M.quasicoherentDataOfIsFinitePresentation.presentation i).relations.I :=
    h.exists_quasicoherentData.choose_spec i
  this.2
end
instance [M.IsFinitePresentation] : M.IsFiniteType where
  exists_localGeneratorsData :=
    ⟨M.quasicoherentDataOfIsFinitePresentation.localGeneratorsData,
      by intro; dsimp; infer_instance⟩
end SheafOfModules