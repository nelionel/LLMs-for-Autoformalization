import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.GroupWithZero.Hom
namespace MulEquiv
protected theorem isField {A : Type*} (B : Type*) [Semiring A] [Semiring B] (hB : IsField B)
    (e : A ≃* B) : IsField A where
  exists_pair_ne := have ⟨x, y, h⟩ := hB.exists_pair_ne; ⟨e.symm x, e.symm y, e.symm.injective.ne h⟩
  mul_comm := fun x y => e.injective <| by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel := fun h => by
    obtain ⟨a', he⟩ := hB.mul_inv_cancel ((e.injective.ne h).trans_eq <| map_zero e)
    exact ⟨e.symm a', e.injective <| by rw [map_mul, map_one, e.apply_symm_apply, he]⟩
end MulEquiv