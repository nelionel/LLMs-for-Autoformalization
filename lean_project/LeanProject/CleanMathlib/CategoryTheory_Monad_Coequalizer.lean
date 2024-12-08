import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Monad.Algebra
universe v₁ u₁
namespace CategoryTheory
namespace Monad
open Limits
variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Monad C} (X : Algebra T)
@[simps!]
def FreeCoequalizer.topMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A :=
  (Monad.free T).map X.a
@[simps]
def FreeCoequalizer.bottomMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h := T.assoc X.A
@[simps]
def FreeCoequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h := X.assoc.symm
theorem FreeCoequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X =
      FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext X.assoc.symm
instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.unit, Functor.map_id]
  · ext
    apply Monad.right_unit
@[simps!]
def beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)
def beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X) :=
  Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, Category.assoc, h₂, Monad.right_unit_assoc,
        show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _, h₁, Monad.left_unit_assoc]
    · ext
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      apply (X.unit_assoc _).symm
def beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩
@[simps! pt]
def beckCofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork
@[simp]
theorem beckCofork_π : (beckCofork X).π = X.a :=
  rfl
def beckCoequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer
@[simp]
theorem beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) :
    (beckCoequalizer X).desc s = T.η.app _ ≫ s.π :=
  rfl
end Monad
end CategoryTheory