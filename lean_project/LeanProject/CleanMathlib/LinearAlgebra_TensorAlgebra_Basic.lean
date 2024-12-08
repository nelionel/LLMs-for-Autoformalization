import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Multilinear.Basic
variable (R : Type*) [CommSemiring R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
namespace TensorAlgebra
inductive Rel : FreeAlgebra R M → FreeAlgebra R M → Prop
  | add {a b : M} : Rel (FreeAlgebra.ι R (a + b)) (FreeAlgebra.ι R a + FreeAlgebra.ι R b)
  | smul {r : R} {a : M} :
    Rel (FreeAlgebra.ι R (r • a)) (algebraMap R (FreeAlgebra R M) r * FreeAlgebra.ι R a)
end TensorAlgebra
def TensorAlgebra :=
  RingQuot (TensorAlgebra.Rel R M)
instance : Inhabited (TensorAlgebra R M) := RingQuot.instInhabited _
instance : Semiring (TensorAlgebra R M) := RingQuot.instSemiring _
@[nolint unusedArguments]
instance instAlgebra {R A M} [CommSemiring R] [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [Module R M] [Module A M]
    [IsScalarTower R A M] :
    Algebra R (TensorAlgebra A M) :=
  RingQuot.instAlgebra _
example : (Semiring.toNatAlgebra : Algebra ℕ (TensorAlgebra R M)) = instAlgebra := rfl
instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] :
    SMulCommClass R S (TensorAlgebra A M) :=
  RingQuot.instSMulCommClass _
instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S A] :
    IsScalarTower R S (TensorAlgebra A M) :=
  RingQuot.instIsScalarTower _
namespace TensorAlgebra
instance {S : Type*} [CommRing S] [Module S M] : Ring (TensorAlgebra S M) :=
  RingQuot.instRing (Rel S M)
variable (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] in
example : (Ring.toIntAlgebra _ : Algebra ℤ (TensorAlgebra S M)) = instAlgebra := rfl
variable {M}
irreducible_def ι : M →ₗ[R] TensorAlgebra R M :=
  { toFun := fun m => RingQuot.mkAlgHom R _ (FreeAlgebra.ι R m)
    map_add' := fun x y => by
      rw [← map_add (RingQuot.mkAlgHom R (Rel R M))]
      exact RingQuot.mkAlgHom_rel R Rel.add
    map_smul' := fun r x => by
      rw [← map_smul (RingQuot.mkAlgHom R (Rel R M))]
      exact RingQuot.mkAlgHom_rel R Rel.smul }
theorem ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι (m : M) :
    RingQuot.mkAlgHom R (Rel R M) (FreeAlgebra.ι R m) = ι R m := by
  rw [ι]
  rfl
@[simps symm_apply]
def lift {A : Type*} [Semiring A] [Algebra R A] : (M →ₗ[R] A) ≃ (TensorAlgebra R M →ₐ[R] A) :=
  { toFun :=
      RingQuot.liftAlgHom R ∘ fun f =>
        ⟨FreeAlgebra.lift R (⇑f), fun x y (h : Rel R M x y) => by
          induction h <;>
            simp only [Algebra.smul_def, FreeAlgebra.lift_ι_apply, LinearMap.map_smulₛₗ,
              RingHom.id_apply, map_mul, AlgHom.commutes, map_add]⟩
    invFun := fun F => F.toLinearMap.comp (ι R)
    left_inv := fun f => by
      rw [ι]
      ext1 x
      exact (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply f x)
    right_inv := fun F =>
      RingQuot.ringQuot_ext' _ _ _ <|
        FreeAlgebra.hom_ext <|
          funext fun x => by
            rw [ι]
            exact
              (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply _ _) }
variable {R}
@[simp]
theorem ι_comp_lift {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A) :
    (lift R f).toLinearMap.comp (ι R) = f := by
  convert (lift R).symm_apply_apply f
@[simp]
theorem lift_ι_apply {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A) (x) :
    lift R f (ι R x) = f x := by
  conv_rhs => rw [← ι_comp_lift f]
  rfl
@[simp]
theorem lift_unique {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A)
    (g : TensorAlgebra R M →ₐ[R] A) : g.toLinearMap.comp (ι R) = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq]
  simp only [lift, Equiv.coe_fn_symm_mk]
@[simp]
theorem lift_comp_ι {A : Type*} [Semiring A] [Algebra R A] (g : TensorAlgebra R M →ₐ[R] A) :
    lift R (g.toLinearMap.comp (ι R)) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g
@[ext]
theorem hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : TensorAlgebra R M →ₐ[R] A}
    (w : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.injective w
@[elab_as_elim]
theorem induction {C : TensorAlgebra R M → Prop}
    (algebraMap : ∀ r, C (algebraMap R (TensorAlgebra R M) r)) (ι : ∀ x, C (ι R x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : TensorAlgebra R M) : C a := by
  let s : Subalgebra R (TensorAlgebra R M) :=
    { carrier := C
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let h : AddCommMonoid s := inferInstanceAs (AddCommMonoid (Subalgebra.toSubmodule s))
  let of : M →ₗ[R] s := (TensorAlgebra.ι R).codRestrict (Subalgebra.toSubmodule s) ι
  have of_id : AlgHom.id R (TensorAlgebra R M) = s.val.comp (lift R of) := by
    ext
    simp only [AlgHom.toLinearMap_id, LinearMap.id_comp, AlgHom.comp_toLinearMap,
      LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, lift_ι_apply,
      Subalgebra.coe_val]
    erw [LinearMap.codRestrict_apply]
  rw [← AlgHom.id_apply (R := R) a, of_id]
  exact Subtype.prop (lift R of a)
def algebraMapInv : TensorAlgebra R M →ₐ[R] R :=
  lift R (0 : M →ₗ[R] R)
variable (M)
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| TensorAlgebra R M) := fun x => by
  simp [algebraMapInv]
@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (TensorAlgebra R M) x = algebraMap R (TensorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff
@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (TensorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (TensorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
instance [Nontrivial R] : Nontrivial (TensorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial
variable {M}
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    TensorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R (TrivSqZeroExt.inrHom R M)
@[simp]
theorem toTrivSqZeroExt_ι (x : M) [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _
def ιInv : TensorAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap
theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M → TensorAlgebra R M) := fun x ↦ by
  simp [ιInv]
variable (R)
@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff
@[simp]
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, LinearMap.map_zero]
variable {R}
@[simp]
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := lift_ι_apply _ _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [LinearMap.map_zero, RingHom.map_zero]
@[simp]
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (TensorAlgebra R M)).map_one, Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M))
      (1 : Submodule R (TensorAlgebra R M)) := by
  rw [Submodule.disjoint_def, Submodule.one_eq_range]
  rintro _ ⟨x, hx⟩ ⟨r, rfl⟩
  rw [Algebra.linearMap_apply, ι_eq_algebraMap_iff] at hx
  rw [hx.2, map_zero]
variable (R M)
def tprod (n : ℕ) : MultilinearMap R (fun _ : Fin n => M) (TensorAlgebra R M) :=
  (MultilinearMap.mkPiAlgebraFin R n (TensorAlgebra R M)).compLinearMap fun _ => ι R
@[simp]
theorem tprod_apply {n : ℕ} (x : Fin n → M) : tprod R M n x = (List.ofFn fun i => ι R (x i)).prod :=
  rfl
variable {R M}
end TensorAlgebra
namespace FreeAlgebra
variable {R M}
def toTensor : FreeAlgebra R M →ₐ[R] TensorAlgebra R M :=
  FreeAlgebra.lift R (TensorAlgebra.ι R)
@[simp]
theorem toTensor_ι (m : M) : FreeAlgebra.toTensor (FreeAlgebra.ι R m) = TensorAlgebra.ι R m := by
  simp [toTensor]
end FreeAlgebra