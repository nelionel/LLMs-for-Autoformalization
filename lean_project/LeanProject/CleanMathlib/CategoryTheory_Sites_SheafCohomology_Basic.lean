import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
universe w' w v u
namespace CategoryTheory
open Abelian
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
namespace Sheaf
section
variable (F : Sheaf J AddCommGrp.{w})
  [HasSheafify J AddCommGrp.{w}] [HasExt.{w'} (Sheaf J AddCommGrp.{w})]
def H (n : ℕ) : Type w' :=
  Ext ((constantSheaf J AddCommGrp.{w}).obj (AddCommGrp.of (ULift ℤ))) F n
noncomputable instance (n : ℕ) : AddCommGroup (F.H n) := by
  dsimp only [H]
  infer_instance
end
section
variable [HasSheafify J AddCommGrp.{v}] [HasExt.{w'} (Sheaf J AddCommGrp.{v})]
variable (J) in
noncomputable def cohomologyPresheafFunctor (n : ℕ) :
    Sheaf J AddCommGrp.{v} ⥤ Cᵒᵖ ⥤ AddCommGrp.{w'} :=
  Functor.flip
    (Functor.op (yoneda ⋙ (whiskeringRight _ _ _).obj
      AddCommGrp.free ⋙ presheafToSheaf _ _) ⋙ extFunctor n)
noncomputable abbrev cohomologyPresheaf (F : Sheaf J AddCommGrp.{v}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrp.{w'} :=
  (cohomologyPresheafFunctor J n).obj F
end
end Sheaf
end CategoryTheory