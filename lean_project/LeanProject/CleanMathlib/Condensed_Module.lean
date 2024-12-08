import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Condensed.Basic
universe u
open CategoryTheory
variable (R : Type (u+1)) [Ring R]
abbrev CondensedMod := Condensed.{u} (ModuleCat.{u+1} R)
noncomputable instance : Abelian (CondensedMod.{u} R) := sheafIsAbelian
def Condensed.forget : CondensedMod R ⥤ CondensedSet := sheafCompose _ (CategoryTheory.forget _)
noncomputable
def Condensed.free : CondensedSet ⥤ CondensedMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)
noncomputable
def Condensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)
abbrev CondensedAb := CondensedMod.{u} (ULift ℤ)
noncomputable example : Abelian CondensedAb.{u} := inferInstance
abbrev Condensed.abForget : CondensedAb ⥤ CondensedSet := forget _
noncomputable abbrev Condensed.freeAb : CondensedSet ⥤ CondensedAb := free _
noncomputable abbrev Condensed.setAbAdjunction : freeAb ⊣ abForget := freeForgetAdjunction _
namespace CondensedMod
@[simp]
lemma hom_naturality_apply {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x
end CondensedMod