import Mathlib.Logic.Small.Group
import Mathlib.Logic.Small.Ring
noncomputable section
variable {α β : Type*}
instance [Semiring α] [AddCommMonoid β] [Module α β] [Small β] : Module α (Shrink β) :=
  (equivShrink _).symm.module α
def linearEquivShrink (α β) [Semiring α] [AddCommMonoid β] [Module α β] [Small β] :
    β ≃ₗ[α] Shrink β :=
  ((equivShrink β).symm.linearEquiv α).symm
instance [CommSemiring α] [Semiring β] [Algebra α β] [Small β] : Algebra α (Shrink β) :=
  (equivShrink _).symm.algebra α
def algEquivShrink (α β) [CommSemiring α] [Semiring β] [Algebra α β] [Small β] :
    β ≃ₐ[α] Shrink β :=
  ((equivShrink β).symm.algEquiv α).symm