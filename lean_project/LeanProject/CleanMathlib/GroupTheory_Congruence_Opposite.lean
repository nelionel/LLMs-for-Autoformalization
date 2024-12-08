import Mathlib.Algebra.Opposites
import Mathlib.GroupTheory.Congruence.Defs
variable {M : Type*} [Mul M]
namespace Con
@[to_additive "If `c` is an additive congruence on `M`, then `(a, b) ↦ c b.unop a.unop` is an
additive congruence on `Mᵃᵒᵖ`"]
def op (c : Con M) : Con Mᵐᵒᵖ where
  r a b := c b.unop a.unop
  iseqv :=
  { refl := fun a ↦ c.refl a.unop
    symm := c.symm
    trans := fun h1 h2 ↦ c.trans h2 h1 }
  mul' h1 h2 := c.mul h2 h1
@[to_additive "If `c` is an additive congruence on `Mᵃᵒᵖ`, then `(a, b) ↦ c bᵒᵖ aᵒᵖ` is an additive
congruence on `M`"]
def unop (c : Con Mᵐᵒᵖ) : Con M where
  r a b := c (.op b) (.op a)
  iseqv :=
  { refl := fun a ↦ c.refl (.op a)
    symm := c.symm
    trans := fun h1 h2 ↦ c.trans h2 h1 }
  mul' h1 h2 := c.mul h2 h1
@[to_additive (attr := simps) "The additive congruences on `M` bijects to the additive congruences
on `Mᵃᵒᵖ`"]
def orderIsoOp : Con M ≃o Con Mᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'
end Con