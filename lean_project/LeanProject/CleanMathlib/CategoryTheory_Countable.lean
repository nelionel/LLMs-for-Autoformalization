import Mathlib.Data.Countable.Small
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Fintype.Card
universe w v u
open scoped Classical
noncomputable section
namespace CategoryTheory
instance discreteCountable {α : Type*} [Countable α] : Countable (Discrete α) :=
  Countable.of_equiv α discreteEquiv.symm
class CountableCategory (J : Type*) [Category J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : ∀ j j' : J, Countable (j ⟶ j') := by infer_instance
attribute [instance] CountableCategory.countableObj CountableCategory.countableHom
instance countablerCategoryDiscreteOfCountable (J : Type*) [Countable J] :
    CountableCategory (Discrete J) where
instance : CountableCategory ℕ where
namespace CountableCategory
variable (α : Type u) [Category.{v} α] [CountableCategory α]
abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm
instance : Countable (ObjAsType α) := Countable.of_equiv α (equivShrink.{0} α)
instance {i j : ObjAsType α} : Countable (i ⟶ j) :=
  CountableCategory.countableHom ((equivShrink.{0} α).symm i) _
instance : CountableCategory (ObjAsType α) where
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence
def HomAsType := ShrinkHoms (ObjAsType α)
instance : LocallySmall.{0} (ObjAsType α) where
  hom_small _ _ := inferInstance
instance : SmallCategory (HomAsType α) := inferInstanceAs <| SmallCategory (ShrinkHoms _)
instance : Countable (HomAsType α) := Countable.of_equiv α (equivShrink.{0} α)
instance {i j : HomAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv ((ShrinkHoms.equivalence _).inverse.obj i ⟶
    (ShrinkHoms.equivalence _).inverse.obj j)
    (Functor.FullyFaithful.ofFullyFaithful _).homEquiv.symm
instance : CountableCategory (HomAsType α) where
noncomputable def homAsTypeEquiv : HomAsType α ≌ α :=
  (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)
end CountableCategory
instance (α : Type*) [Category α] [FinCategory α] : CountableCategory α where
instance : CountableCategory ℕ where
open Opposite
instance countableCategoryOpposite {J : Type*} [Category J] [CountableCategory J] :
    CountableCategory Jᵒᵖ where
  countableObj := Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm
instance countableCategoryUlift {J : Type v} [Category J] [CountableCategory J] :
    CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  countableObj := instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift
end CategoryTheory