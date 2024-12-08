import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Ring.Subring.Defs
section Ring
variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]
variable (S : Subring R)
open MulAction
variable {R}
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S
instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.eq <| one_smul M (s : R)
  mul_smul m₁ m₂ s := Subtype.eq <| mul_smul m₁ m₂ (s : R)
  smul_add m s₁ s₂ := Subtype.eq <| smul_add m (s₁ : R) (s₂ : R)
  smul_zero m := Subtype.eq <| smul_zero m
  smul_one m := Subtype.eq <| smul_one m
  smul_mul m s₁ s₂ := Subtype.eq <| smul_mul' m (s₁ : R) (s₂ : R)
end Ring
section
variable (M : Type*) [Monoid M]
variable {R' : Type*} [Ring R'] [MulSemiringAction M R']
variable (U : Subring R') [IsInvariantSubring M U]
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ ↦ rfl }
@[simp]
theorem IsInvariantSubring.coe_subtypeHom :
    (IsInvariantSubring.subtypeHom M U : U → R') = Subtype.val := rfl
@[simp]
theorem IsInvariantSubring.coe_subtypeHom' :
    ((IsInvariantSubring.subtypeHom M U).toRingHom : U →+* R') = U.subtype := rfl
end