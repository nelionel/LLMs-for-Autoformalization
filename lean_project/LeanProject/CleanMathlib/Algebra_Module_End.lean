import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
assert_not_exists Multiset
assert_not_exists Set.indicator
assert_not_exists Pi.single_smul₀
assert_not_exists Field
open Function Set
universe u v
variable {R S M M₂ : Type*}
section AddCommMonoid
variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)
theorem AddMonoid.End.natCast_def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n :=
  rfl
variable (R M)
@[simps! apply_apply]
def Module.toAddMonoidEnd : R →+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    map_zero' := AddMonoidHom.ext fun r => show (0 : R) • r = 0 by simp
    map_add' := fun x y =>
      AddMonoidHom.ext fun r => show (x + y) • r = x • r + y • r by simp [add_smul] }
def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom
variable {R M}
@[simp]
theorem smulAddHom_apply (r : R) (x : M) : smulAddHom R M r x = r • x :=
  rfl
end AddCommMonoid
section AddCommGroup
variable (R M) [Semiring R] [AddCommGroup M]
theorem AddMonoid.End.intCast_def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z :=
  rfl
end AddCommGroup
section AddCommGroup
variable [Ring R] [AddCommGroup M] [Module R M]
section
variable (R)
lemma Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b :=
  have : ((smulAddHom R M).flip b).comp (Int.castAddHom R) = (smulAddHom ℤ M).flip b := by
    apply AddMonoidHom.ext_int
    simp
  DFunLike.congr_fun this n
@[deprecated (since := "2024-07-23")] alias intCast_smul := Int.cast_smul_eq_zsmul
@[deprecated Int.cast_smul_eq_zsmul (since := "2024-07-23")]
theorem zsmul_eq_smul_cast (n : ℤ) (b : M) : n • b = (n : R) • b := (Int.cast_smul_eq_zsmul ..).symm
end
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : @SMul.smul ℤ M h.toSMul n x = n • x :=
  Int.cast_smul_eq_zsmul ..
def AddCommGroup.uniqueIntModule : Unique (Module ℤ M) where
  default := by infer_instance
  uniq P := (Module.ext' P _) fun n => by convert int_smul_eq_zsmul P n
end AddCommGroup
theorem map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M] [Module S M₂]
    (x : ℤ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]
instance AddCommGroup.intIsScalarTower {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] : IsScalarTower ℤ R M where
  smul_assoc n x y := ((smulAddHom R M).flip y).map_zsmul x n