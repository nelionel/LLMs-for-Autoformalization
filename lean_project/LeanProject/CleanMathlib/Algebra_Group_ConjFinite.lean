import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Fintype.Units
variable {α : Type*} [Monoid α]
attribute [local instance] IsConj.setoid
instance [Fintype α] [DecidableRel (IsConj : α → α → Prop)] : Fintype (ConjClasses α) :=
  Quotient.fintype (IsConj.setoid α)
instance [Finite α] : Finite (ConjClasses α) :=
  Quotient.finite _
instance [DecidableEq α] [Fintype α] : DecidableRel (IsConj : α → α → Prop) := fun a b =>
  inferInstanceAs (Decidable (∃ c : αˣ, c.1 * a = b * c.1))
instance conjugatesOf.fintype [Fintype α] [DecidableRel (IsConj : α → α → Prop)] {a : α} :
  Fintype (conjugatesOf a) :=
  @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _
namespace ConjClasses
variable [Fintype α] [DecidableRel (IsConj : α → α → Prop)]
instance {x : ConjClasses α} : Fintype (carrier x) :=
  Quotient.recOnSubsingleton x fun _ => conjugatesOf.fintype
end ConjClasses