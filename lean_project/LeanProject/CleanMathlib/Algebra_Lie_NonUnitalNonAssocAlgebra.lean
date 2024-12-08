import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Lie.Basic
universe u v w
variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
def CommutatorRing (L : Type v) : Type v := L
instance : NonUnitalNonAssocRing (CommutatorRing L) :=
  show NonUnitalNonAssocRing L from
    { (inferInstance : AddCommGroup L) with
      mul := Bracket.bracket
      left_distrib := lie_add
      right_distrib := add_lie
      zero_mul := zero_lie
      mul_zero := lie_zero }
namespace LieAlgebra
instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) := ‹Nonempty L›
instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) := ‹Inhabited L›
instance : LieRing (CommutatorRing L) := show LieRing L by infer_instance
instance : LieAlgebra R (CommutatorRing L) := show LieAlgebra R L by infer_instance
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) := ⟨smul_lie⟩
instance smulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩
end LieAlgebra
namespace LieHom
variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]
@[simps]
def toNonUnitalAlgHom (f : L →ₗ⁅R⁆ L₂) : CommutatorRing L →ₙₐ[R] CommutatorRing L₂ :=
  { f with
    toFun := f
    map_zero' := f.map_zero
    map_mul' := f.map_lie }
theorem toNonUnitalAlgHom_injective :
    Function.Injective (toNonUnitalAlgHom : _ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂) :=
  fun _ _ h => ext <| NonUnitalAlgHom.congr_fun h
end LieHom