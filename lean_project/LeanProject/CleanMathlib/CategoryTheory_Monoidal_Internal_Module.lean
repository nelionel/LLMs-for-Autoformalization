import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
suppress_compilation
universe v u
open CategoryTheory
open LinearMap
open scoped TensorProduct
attribute [local ext] TensorProduct.ext
namespace ModuleCat
variable {R : Type u} [CommRing R]
namespace MonModuleEquivalenceAlgebra
instance Ring_of_Mon_ (A : Mon_ (ModuleCat.{u} R)) : Ring A.X :=
  { (inferInstance : AddCommGroup A.X) with
    one := A.one (1 : R)
    mul := fun x y => A.mul (x ⊗ₜ y)
    one_mul := fun x => by
      convert LinearMap.congr_fun A.one_mul ((1 : R) ⊗ₜ x)
      rw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_one := fun x => by
      convert LinearMap.congr_fun A.mul_one (x ⊗ₜ (1 : R))
      erw [MonoidalCategory.leftUnitor_hom_apply, one_smul]
    mul_assoc := fun x y z => by
      convert LinearMap.congr_fun A.mul_assoc (x ⊗ₜ y ⊗ₜ z)
    left_distrib := fun x y z => by
      convert A.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z)
      rw [← TensorProduct.tmul_add]
      rfl
    right_distrib := fun x y z => by
      convert A.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z)
      rw [← TensorProduct.add_tmul]
      rfl
    zero_mul := fun x => show A.mul _ = 0 by
      rw [TensorProduct.zero_tmul, map_zero]
    mul_zero := fun x => show A.mul _ = 0 by
      rw [TensorProduct.tmul_zero, map_zero] }
instance Algebra_of_Mon_ (A : Mon_ (ModuleCat.{u} R)) : Algebra R A.X :=
  { A.one with
    map_zero' := A.one.map_zero
    map_one' := rfl
    map_mul' := fun x y => by
      have h := LinearMap.congr_fun A.one_mul.symm (x ⊗ₜ A.one y)
      rwa [MonoidalCategory.leftUnitor_hom_apply, ← A.one.map_smul] at h
    commutes' := fun r a => by
      dsimp
      have h₁ := LinearMap.congr_fun A.one_mul (r ⊗ₜ a)
      have h₂ := LinearMap.congr_fun A.mul_one (a ⊗ₜ r)
      exact h₁.trans h₂.symm
    smul_def' := fun r a => (LinearMap.congr_fun A.one_mul (r ⊗ₜ a)).symm }
@[simp]
theorem algebraMap (A : Mon_ (ModuleCat.{u} R)) (r : R) : algebraMap R A.X r = A.one r :=
  rfl
@[simps!]
def functor : Mon_ (ModuleCat.{u} R) ⥤ AlgebraCat R where
  obj A := AlgebraCat.of R A.X
  map {_ _} f := AlgebraCat.ofHom
    { f.hom.toAddMonoidHom with
      toFun := f.hom
      map_one' := LinearMap.congr_fun f.one_hom (1 : R)
      map_mul' := fun x y => LinearMap.congr_fun f.mul_hom (x ⊗ₜ y)
      commutes' := fun r => LinearMap.congr_fun f.one_hom r }
@[simps]
def inverseObj (A : AlgebraCat.{u} R) : Mon_ (ModuleCat.{u} R) where
  X := ModuleCat.of R A
  one := Algebra.linearMap R A
  mul := LinearMap.mul' R A
  one_mul := by
    refine TensorProduct.ext <| LinearMap.ext_ring <| LinearMap.ext fun x => ?_
    erw [compr₂_apply, compr₂_apply, CategoryTheory.comp_apply]
    erw [LinearMap.mul'_apply, MonoidalCategory.leftUnitor_hom_apply, ← Algebra.smul_def]
    erw [id_apply]
  mul_one := by
    refine TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext_ring ?_
    erw [compr₂_apply, compr₂_apply]
    erw [CategoryTheory.comp_apply]
    erw [LinearMap.mul'_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, ← Algebra.commutes,
      ← Algebra.smul_def]
    erw [id_apply]
  mul_assoc := by
    set_option tactic.skipAssignedInstances false in
    refine TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext fun x => LinearMap.ext fun y =>
      LinearMap.ext fun z => ?_
    dsimp only [compr₂_apply, TensorProduct.mk_apply]
    rw [compr₂_apply, compr₂_apply]
    erw [CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, CategoryTheory.comp_apply]
    erw [LinearMap.mul'_apply, LinearMap.mul'_apply]
    erw [id_apply]
    erw [TensorProduct.mk_apply, TensorProduct.mk_apply, mul'_apply, LinearMap.id_apply, mul'_apply]
    simp only [LinearMap.mul'_apply, mul_assoc]
@[simps]
def inverse : AlgebraCat.{u} R ⥤ Mon_ (ModuleCat.{u} R) where
  obj := inverseObj
  map f :=
    { hom := f.hom.toLinearMap
      one_hom := LinearMap.ext f.hom.commutes
      mul_hom := TensorProduct.ext <| LinearMap.ext₂ <| map_mul f.hom }
end MonModuleEquivalenceAlgebra
open MonModuleEquivalenceAlgebra
set_option maxHeartbeats 400000 in
def monModuleEquivalenceAlgebra : Mon_ (ModuleCat.{u} R) ≌ AlgebraCat R where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { hom :=
                { toFun := _root_.id
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              mul_hom := by
                refine TensorProduct.ext ?_
                dsimp at *
                rfl }
          inv :=
            { hom :=
                { toFun := _root_.id
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              mul_hom := by
                refine TensorProduct.ext ?_
                dsimp at *
                rfl } })
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := AlgebraCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one
              map_mul' := fun x y => @LinearMap.mul'_apply R _ _ _ _ _ _ x y
              commutes' := fun _ => rfl }
          inv := AlgebraCat.ofHom
            { toFun := _root_.id
              map_zero' := rfl
              map_add' := fun _ _ => rfl
              map_one' := (algebraMap R A).map_one.symm
              map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
              commutes' := fun _ => rfl } })
def monModuleEquivalenceAlgebraForget :
    MonModuleEquivalenceAlgebra.functor ⋙ forget₂ (AlgebraCat.{u} R) (ModuleCat.{u} R) ≅
      Mon_.forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        inv :=
          { toFun := _root_.id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl } })
end ModuleCat