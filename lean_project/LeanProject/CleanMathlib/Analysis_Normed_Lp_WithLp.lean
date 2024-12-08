import Mathlib.Data.ENNReal.Basic
import Mathlib.RingTheory.Finiteness.Defs
open scoped ENNReal
universe uK uK' uV
@[nolint unusedArguments]
def WithLp (_p : ℝ≥0∞) (V : Type uV) : Type uV := V
variable (p : ℝ≥0∞) (K : Type uK) (K' : Type uK') (V : Type uV)
namespace WithLp
protected def equiv : WithLp p V ≃ V := Equiv.refl _
instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := ‹Nontrivial V›
instance instUnique [Unique V] : Unique (WithLp p V) := ‹Unique V›
variable [Semiring K] [Semiring K'] [AddCommGroup V]
instance instAddCommGroup : AddCommGroup (WithLp p V) := ‹AddCommGroup V›
instance instModule [Module K V] : Module K (WithLp p V) := ‹Module K V›
instance instIsScalarTower [SMul K K'] [Module K V] [Module K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  ‹IsScalarTower K K' V›
instance instSMulCommClass [Module K V] [Module K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  ‹SMulCommClass K K' V›
instance instModuleFinite [Module K V] [Module.Finite K V] : Module.Finite K (WithLp p V) :=
  ‹Module.Finite K V›
variable {K V}
variable [Module K V]
variable (c : K) (x y : WithLp p V) (x' y' : V)
@[simp]
theorem equiv_zero : WithLp.equiv p V 0 = 0 :=
  rfl
@[simp]
theorem equiv_symm_zero : (WithLp.equiv p V).symm 0 = 0 :=
  rfl
@[simp]
theorem equiv_add : WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl
@[simp]
theorem equiv_symm_add :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl
@[simp]
theorem equiv_sub : WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl
@[simp]
theorem equiv_symm_sub :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl
@[simp]
theorem equiv_neg : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl
@[simp]
theorem equiv_symm_neg : (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl
@[simp]
theorem equiv_smul : WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl
@[simp]
theorem equiv_symm_smul : (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl
variable (K V)
@[simps (config := .asFn)]
protected def linearEquiv : WithLp p V ≃ₗ[K] V :=
  { LinearEquiv.refl _ _ with
    toFun := WithLp.equiv _ _
    invFun := (WithLp.equiv _ _).symm }
end WithLp