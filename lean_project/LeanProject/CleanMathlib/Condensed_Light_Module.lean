import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
universe u
open CategoryTheory
variable (R : Type u) [Ring R]
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)
noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)
noncomputable
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)
noncomputable
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R :=  Sheaf.adjunction _ (ModuleCat.adj R)
abbrev LightCondAb := LightCondMod ℤ
noncomputable example : Abelian LightCondAb := inferInstance
namespace LightCondMod
@[simp]
lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x
end LightCondMod