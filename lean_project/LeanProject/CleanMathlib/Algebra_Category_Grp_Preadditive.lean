import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
open CategoryTheory
universe u
namespace AddCommGrp
instance (P Q : AddCommGrp) : AddCommGroup (P ⟶ Q) :=
  (inferInstance : AddCommGroup (AddMonoidHom P Q))
@[simp]
lemma hom_add_apply {P Q : AddCommGrp} (f g : P ⟶ Q) (x : P) : (f + g) x = f x + g x := rfl
section
attribute [-simp] Preadditive.add_comp Preadditive.comp_add
instance : Preadditive AddCommGrp where
end
end AddCommGrp