import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
import Mathlib.CategoryTheory.Monad.Algebra
universe v₁ u₁
namespace CategoryTheory
namespace Comonad
open Limits
variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Comonad C} (X : Coalgebra T)
@[simps!]
def CofreeEqualizer.topMap :  (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) :=
  (Comonad.cofree T).map X.a
@[simps]
def CofreeEqualizer.bottomMap :
    (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) where
  f := T.δ.app X.A
  h := T.coassoc X.A
@[simps]
def CofreeEqualizer.ι : X ⟶ (Comonad.cofree T).obj X.A where
  f := X.a
  h := X.coassoc.symm
theorem CofreeEqualizer.condition :
    CofreeEqualizer.ι X ≫ CofreeEqualizer.topMap X =
      CofreeEqualizer.ι X ≫ CofreeEqualizer.bottomMap X :=
  Coalgebra.Hom.ext X.coassoc.symm
instance : IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) := by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.counit, Functor.map_id]
  · ext
    apply Comonad.right_counit
@[simps!]
def beckCoalgebraFork : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) :=
  Fork.ofι _ (CofreeEqualizer.condition X)
def beckCoalgebraEqualizer : IsLimit (beckCoalgebraFork X) :=
  Fork.IsLimit.mk' _ fun s => by
    have h₁ :  s.ι.f  ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ :  s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, reassoc_of% h₂, Comonad.right_counit]
      dsimp
      rw [Category.comp_id, Category.assoc]
      erw [← T.ε.naturality, reassoc_of% h₁, Comonad.left_counit] 
      simp
    · ext
      simpa [← T.ε.naturality_assoc, T.left_counit_assoc] using h₁ =≫ T.ε.app ((T : C ⥤ C).obj X.A)
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      simp [beckCoalgebraFork, X.counit]
def beckSplitEqualizer : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a :=
  ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩
@[simps! pt]
def beckFork : Fork (T.map X.a) (T.δ.app _) :=
  (beckSplitEqualizer X).asFork
@[simp]
theorem beckFork_ι : (beckFork X).ι = X.a :=
  rfl
def beckEqualizer : IsLimit (beckFork X) :=
  (beckSplitEqualizer X).isEqualizer
@[simp]
theorem beckEqualizer_lift (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)) :
    (beckEqualizer X).lift s = s.ι ≫ T.ε.app _ :=
  rfl
end Comonad
end CategoryTheory