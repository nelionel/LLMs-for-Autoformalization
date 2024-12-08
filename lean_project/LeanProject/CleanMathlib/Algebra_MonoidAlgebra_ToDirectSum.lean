import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}
open DirectSum
section Defs
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  Finsupp.toDFinsupp f
section
variable [DecidableEq ι] [Semiring M]
@[simp]
theorem AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) :
    AddMonoidAlgebra.toDirectSum (Finsupp.single i m) = DirectSum.of _ i m :=
  Finsupp.toDFinsupp_single i m
variable [∀ m : M, Decidable (m ≠ 0)]
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι :=
  DFinsupp.toFinsupp f
@[simp]
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = Finsupp.single i m :=
  DFinsupp.toFinsupp_single i m
@[simp]
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f :=
  Finsupp.toDFinsupp_toFinsupp f
@[simp]
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) : _)
end
end Defs
section Lemmas
namespace AddMonoidAlgebra
@[simp]
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero
@[simp]
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _
@[simp]
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  show to_hom (f * g) = to_hom f * to_hom g
  let _ : NonUnitalNonAssocSemiring (ι →₀ M) := AddMonoidAlgebra.nonUnitalNonAssocSemiring
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  refine Finsupp.addHom_ext' fun xi => AddMonoidHom.ext fun xv => ?_
  refine Finsupp.addHom_ext' fun yi => AddMonoidHom.ext fun yv => ?_
  dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply,
    AddMonoidHom.mul_apply, Finsupp.singleAddHom_apply]
  erw [AddMonoidHom.compl₂_apply]
  rw [AddMonoidHom.coe_mk, AddMonoidHom.coe_mk]
  erw [AddMonoidHom.coe_mk]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toDirectSum_single]
  dsimp
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidHom.coe_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddMonoidAlgebra.toDirectSum_single]
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Function.comp_apply, toDirectSum_single, AddMonoidHom.id_apply, Finsupp.singleAddHom_apply,
    AddMonoidHom.coe_mulLeft]
  rw [DirectSum.of_mul_of, Mul.gMul_mul]
end AddMonoidAlgebra
namespace DirectSum
variable [DecidableEq ι]
@[simp]
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) :=
  DFinsupp.toFinsupp_zero
@[simp]
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g :=
  DFinsupp.toFinsupp_add _ _
@[simp]
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
end DirectSum
end Lemmas
section Equivs
@[simps (config := .asFn)]
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra }
@[simps (config := .asFn)]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M :=
  { addMonoidAlgebraEquivDirectSum with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_add' := AddMonoidAlgebra.toDirectSum_add }
@[simps (config := .asFn)]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }
@[simps (config := .asFn)]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }
end Equivs