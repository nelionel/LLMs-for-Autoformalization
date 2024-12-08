import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.Algebra.Category.CoalgebraCat.Basic
universe v u
namespace CoalgebraCat
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R]
@[simps] def toComonObj (X : CoalgebraCat R) : Comon_ (ModuleCat R) where
  X := ModuleCat.of R X
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := by simpa only [ModuleCat.of_coe] using Coalgebra.rTensor_counit_comp_comul
  comul_counit := by simpa only [ModuleCat.of_coe] using Coalgebra.lTensor_counit_comp_comul
  comul_assoc := by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm
variable (R) in
@[simps]
def toComon : CoalgebraCat R ⥤ Comon_ (ModuleCat R) where
  obj X := toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      hom_counit := f.1.counit_comp
      hom_comul := f.1.map_comp_comul.symm }
@[simps]
instance ofComonObjCoalgebraStruct (X : Comon_ (ModuleCat R)) :
    CoalgebraStruct R X.X where
  comul := X.comul
  counit := X.counit
def ofComonObj (X : Comon_ (ModuleCat R)) : CoalgebraCat R where
  carrier := X.X
  instCoalgebra :=
    { ofComonObjCoalgebraStruct X with
      coassoc := X.comul_assoc.symm
      rTensor_counit_comp_comul := X.counit_comul
      lTensor_counit_comp_comul := X.comul_counit }
variable (R)
def ofComon : Comon_ (ModuleCat R) ⥤ CoalgebraCat R where
  obj X := ofComonObj X
  map f :=
    { toCoalgHom :=
      { f.hom with
        counit_comp := f.hom_counit
        map_comp_comul := f.hom_comul.symm }}
@[simps]
noncomputable def comonEquivalence : CoalgebraCat R ≌ Comon_ (ModuleCat R) where
  functor := toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
variable {R}
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgebraCat R) :=
  Monoidal.transport (comonEquivalence R).symm
namespace MonoidalCategoryAux
variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]
attribute [local instance] instMonoidalCategoryAux
open MonoidalCategory ModuleCat.MonoidalCategory
theorem tensorObj_comul (K L : CoalgebraCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgebraCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, ModuleCat.of_coe, toComonObj_comul,
    tensorμ_eq_tensorTensorTensorComm]
  rfl
theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgebraCat.ofHom f ⊗ CoalgebraCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl
theorem associator_hom_toLinearMap :
    (α_ (CoalgebraCat.of R M) (CoalgebraCat.of R N) (CoalgebraCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgebraCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl
theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgebraCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl
open TensorProduct
theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, of_carrier, of_isAddCommGroup,
    of_isModule, toComonObj_comul, of_instCoalgebra, tensorμ_eq_tensorTensorTensorComm]
  rfl
theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗
      (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, of_carrier, of_isAddCommGroup,
    of_isModule, ModuleCat.of_coe, toComonObj_comul, of_instCoalgebra]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, Comon_.monoidal_tensorObj_comul, toComonObj_X, of_carrier, of_isAddCommGroup,
    of_isModule, toComonObj_comul, of_instCoalgebra, tensorμ_eq_tensorTensorTensorComm]
  rfl
theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.comul (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, ModuleCat.of_coe, of_carrier,
    of_isAddCommGroup, of_isModule, toComonObj_comul, of_instCoalgebra]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, Comon_.monoidal_tensorObj_comul, toComonObj_X, of_carrier, of_isAddCommGroup,
    of_isModule, toComonObj_comul, of_instCoalgebra, tensorμ_eq_tensorTensorTensorComm]
  rfl
theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] N) := by
  rfl
theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgebraCat.of R M ⊗ (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) := by
  ext; rfl
theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) := by
  ext; rfl
end CoalgebraCat.MonoidalCategoryAux