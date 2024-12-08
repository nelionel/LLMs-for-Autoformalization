import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.Basic
assert_not_exists Equiv.Perm.cycleType
suppress_compilation
open scoped TensorProduct
open TensorProduct
namespace LinearMap
open TensorProduct
section Semiring
variable {R A B M N P : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]
variable (r : R) (f g : M →ₗ[R] N)
variable (A)
def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f
variable {A}
@[simp]
theorem baseChange_tmul (a : A) (x : M) : f.baseChange A (a ⊗ₜ x) = a ⊗ₜ f x :=
  rfl
theorem baseChange_eq_ltensor : (f.baseChange A : A ⊗ M → A ⊗ N) = f.lTensor A :=
  rfl
@[simp]
theorem baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]
@[simp]
theorem baseChange_zero : baseChange A (0 : M →ₗ[R] N) = 0 := by
  ext
  simp [baseChange_eq_ltensor]
@[simp]
theorem baseChange_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp [baseChange_tmul]
@[simp]
lemma baseChange_id : (.id : M →ₗ[R] M).baseChange A = .id := by
  ext; simp
lemma baseChange_comp (g : N →ₗ[R] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A := by
  ext; simp
variable (R M) in
@[simp]
lemma baseChange_one : (1 : Module.End R M).baseChange A = 1 := baseChange_id
lemma baseChange_mul (f g : Module.End R M) :
    (f * g).baseChange A = f.baseChange A * g.baseChange A := by
  ext; simp
variable (R A M N)
def _root_.LinearEquiv.baseChange (e : M ≃ₗ[R] N) : A ⊗[R] M ≃ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.congr (.refl _ _) e
@[simps]
def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul
@[simps!]
def _root_.Module.End.baseChangeHom : Module.End R M →ₐ[R] Module.End A (A ⊗[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul
lemma baseChange_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n
end Semiring
section Ring
variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M →ₗ[R] N)
@[simp]
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, tmul_sub]
@[simp]
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, tmul_neg]
end Ring
section liftBaseChange
variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]
noncomputable
def liftBaseChangeEquiv : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)
noncomputable
abbrev liftBaseChange (l : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l
@[simp]
lemma liftBaseChange_tmul (l : M →ₗ[R] N) (x y) : l.liftBaseChange A (x ⊗ₜ y) = x • l y := rfl
lemma liftBaseChange_one_tmul (l : M →ₗ[R] N) (y) : l.liftBaseChange A (1 ⊗ₜ y) = l y := by simp
@[simp]
lemma liftBaseChangeEquiv_symm_apply (l : A ⊗[R] M →ₗ[A] N) (x) :
    (liftBaseChangeEquiv A).symm l x = l (1 ⊗ₜ x) := rfl
lemma liftBaseChange_comp {P} [AddCommMonoid P] [Module A P] [Module R P] [IsScalarTower R A P]
    (l : M →ₗ[R] N) (l' : N →ₗ[A] P) :
      l' ∘ₗ l.liftBaseChange A = (l'.restrictScalars R ∘ₗ l).liftBaseChange A := by
  ext
  simp
@[simp]
lemma range_liftBaseChange (l : M →ₗ[R] N) :
    LinearMap.range (l.liftBaseChange A) = Submodule.span A (LinearMap.range l) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on
    · simp
    · rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [map_add]
      exact add_mem ‹_› ‹_›
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩
end liftBaseChange
end LinearMap
namespace Algebra
namespace TensorProduct
universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {S : Type uS}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}
section AddCommMonoidWithOne
variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]
instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1
theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
instance instAddCommMonoidWithOne : AddCommMonoidWithOne (A ⊗[R] B) where
  natCast n := n ⊗ₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm
theorem natCast_def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl
theorem natCast_def' (n : ℕ) : (n : A ⊗[R] B) = (1 : A) ⊗ₜ (n : B) := by
  rw [natCast_def, ← nsmul_one, smul_tmul, nsmul_one]
end AddCommMonoidWithOne
section NonUnitalNonAssocSemiring
variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
@[irreducible]
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)
unseal mul in
@[simp]
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
instance instMul : Mul (A ⊗[R] B) where
  mul a b := mul a b
unseal mul in
@[simp]
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
unseal mul in
theorem _root_.SemiconjBy.tmul {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha : SemiconjBy a₁ a₂ a₃) (hb : SemiconjBy b₁ b₂ b₃) :
    SemiconjBy (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃) :=
  congr_arg₂ (· ⊗ₜ[R] ·) ha.eq hb.eq
nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) :=
  ha.tmul hb
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
instance (priority := 100) isScalarTower_right [Monoid S] [DistribMulAction S A]
    [IsScalarTower S A A] [SMulCommClass R S A] : IsScalarTower S (A ⊗[R] B) (A ⊗[R] B) where
  smul_assoc r x y := by
    change r • x * y = r • (x * y)
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, smul_mul_assoc]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]
instance (priority := 100) sMulCommClass_right [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [SMulCommClass R S A] : SMulCommClass S (A ⊗[R] B) (A ⊗[R] B) where
  smul_comm r x y := by
    change r • (x * y) = x * r • y
    induction y with
    | zero => simp [smul_zero]
    | tmul a b => induction x with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, mul_smul_comm]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]
end NonUnitalNonAssocSemiring
section NonAssocSemiring
variable [CommSemiring R]
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
protected theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp +contextual
instance instNonAssocSemiring : NonAssocSemiring (A ⊗[R] B) where
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne
end NonAssocSemiring
section NonUnitalSemiring
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
unseal mul in
protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· ⊗ₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)
instance instNonUnitalSemiring : NonUnitalSemiring (A ⊗[R] B) where
  mul_assoc := Algebra.TensorProduct.mul_assoc
end NonUnitalSemiring
section Semiring
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]
instance instSemiring : Semiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ
@[simp]
theorem tmul_pow (a : A) (b : B) (k : ℕ) : a ⊗ₜ[R] b ^ k = (a ^ k) ⊗ₜ[R] (b ^ k) := by
  induction' k with k ih
  · simp [one_def]
  · simp [pow_succ, ih]
@[simps]
def includeLeftRingHom : A →+* A ⊗[R] B where
  toFun a := a ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [add_tmul]
  map_one' := rfl
  map_mul' := by simp
variable [CommSemiring S] [Algebra S A]
instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=
  { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', ← one_def, mul_smul_comm, smul_mul_assoc, mul_one,
        one_mul]
    smul_def' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc, ← one_def, one_mul]
    toRingHom := TensorProduct.includeLeftRingHom.comp (algebraMap S A) }
example : (Semiring.toNatAlgebra : Algebra ℕ (ℕ ⊗[ℕ] B)) = leftAlgebra := rfl
instance instAlgebra : Algebra R (A ⊗[R] B) :=
  inferInstance
@[simp]
theorem algebraMap_apply [SMulCommClass R S A] (r : S) :
    algebraMap S (A ⊗[R] B) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl
theorem algebraMap_apply' (r : R) :
    algebraMap R (A ⊗[R] B) r = 1 ⊗ₜ algebraMap R B r := by
  rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=
  { includeLeftRingHom with commutes' := by simp }
@[simp]
theorem includeLeft_apply [SMulCommClass R S A] (a : A) :
    (includeLeft : A →ₐ[S] A ⊗[R] B) a = a ⊗ₜ 1 :=
  rfl
def includeRight : B →ₐ[R] A ⊗[R] B where
  toFun b := 1 ⊗ₜ b
  map_zero' := by simp
  map_add' := by simp [tmul_add]
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp only [algebraMap_apply']
@[simp]
theorem includeRight_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl
theorem includeLeftRingHom_comp_algebraMap :
    (includeLeftRingHom.comp (algebraMap R A) : R →+* A ⊗[R] B) =
      includeRight.toRingHom.comp (algebraMap R B) := by
  ext
  simp
section ext
variable [Algebra R S] [Algebra S C] [IsScalarTower R S A] [IsScalarTower R S C]
@[ext high]
theorem ext ⦃f g : (A ⊗[R] B) →ₐ[S] C⦄
    (ha : f.comp includeLeft = g.comp includeLeft)
    (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).comp includeRight) :
    f = g := by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← map_mul, ← map_mul, tmul_mul_tmul, one_mul, mul_one] at this
theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
  ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)
end ext
end Semiring
section AddCommGroupWithOne
variable [CommSemiring R]
variable [AddCommGroupWithOne A] [Module R A]
variable [AddCommGroupWithOne B] [Module R B]
instance instAddCommGroupWithOne : AddCommGroupWithOne (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z ⊗ₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]
theorem intCast_def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl
end AddCommGroupWithOne
section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring
end NonUnitalNonAssocRing
section NonAssocRing
variable [CommRing R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
instance instNonAssocRing : NonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne
end NonAssocRing
section NonUnitalRing
variable [CommRing R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
instance instNonUnitalRing : NonUnitalRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring
end NonUnitalRing
section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]
instance instCommSemiring : CommSemiring (A ⊗[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]
end CommSemiring
section Ring
variable [CommRing R]
variable [Ring A] [Algebra R A]
variable [Ring B] [Algebra R B]
instance instRing : Ring (A ⊗[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing
theorem intCast_def' (z : ℤ) : (z : A ⊗[R] B) = (1 : A) ⊗ₜ (z : B) := by
  rw [intCast_def, ← zsmul_one, smul_tmul, zsmul_one]
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
example : (Ring.toIntAlgebra _ : Algebra ℤ (ℤ ⊗[ℤ] B)) = leftAlgebra := rfl
end Ring
section CommRing
variable [CommRing R]
variable [CommRing A] [Algebra R A]
variable [CommRing B] [Algebra R B]
instance instCommRing : CommRing (A ⊗[R] B) :=
  { toRing := inferInstance
    mul_comm := mul_comm }
end CommRing
section RightAlgebra
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]
abbrev rightAlgebra : Algebra B (A ⊗[R] B) :=
  includeRight.toRingHom.toAlgebra' fun b x => by
    suffices LinearMap.mulLeft R (includeRight b) = LinearMap.mulRight R (includeRight b) from
      congr($this x)
    ext xa xb
    simp [mul_comm]
attribute [local instance] TensorProduct.rightAlgebra
instance right_isScalarTower : IsScalarTower R B (A ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm
end RightAlgebra
example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance
example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance
section Monoidal
section
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra S C]
variable [Semiring D] [Algebra R D]
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  #adaptation_note
  AlgHom.ofLinearMap f h_one <| (f.map_mul_iff (R := S) (A := A ⊗[R] B)).2 <| by
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    dsimp
    exact h_mul _ _ _ _
@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }
@[simp]
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl
variable [Algebra R C]
def algEquivOfLinearEquivTripleTensorProduct (f : (A ⊗[R] B) ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    dsimp
    exact h_mul _ _ _ _ _ _
@[simp]
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl
section lift
variable [IsScalarTower R S C]
def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [map_mul, map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [map_one, map_one, one_mul])
@[simp]
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl
@[simp]
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp
@[simp]
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp
@[simp]
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp
@[simps]
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp
end lift
end
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Semiring C] [Algebra R C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E]
variable [Semiring F] [Algebra R F]
section
variable (R A)
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])
@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl
variable {R} {A} in
@[simp]
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl
variable {A} in
@[simp]
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl
variable (S)
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul_comm r₁ a₁ r₂ a₂ |>.symm)
    (one_smul R _)
@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl
variable {R A} in
@[simp]
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl
variable {A} in
@[simp]
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl
section
variable (B)
unseal mul in
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl
@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl
variable {A B} in
@[simp]
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl
variable {A B} in
@[simp]
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b :=
  rfl
theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl
theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)
end
section
variable {R A}
unseal mul in
theorem assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
    (TensorProduct.assoc R A B C) (((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) ⊗ₜ[R] (c₁ * c₂)) =
      (TensorProduct.assoc R A B C) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] c₁) *
        (TensorProduct.assoc R A B C) ((a₂ ⊗ₜ[R] b₂) ⊗ₜ[R] c₂) :=
  rfl
theorem assoc_aux_2 : (TensorProduct.assoc R A B C) ((1 ⊗ₜ[R] 1) ⊗ₜ[R] 1) = 1 :=
  rfl
variable (R A B C)
protected def assoc : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] B ⊗[R] C :=
  algEquivOfLinearEquivTripleTensorProduct
    (_root_.TensorProduct.assoc R A B C)
    Algebra.TensorProduct.assoc_aux_1
    Algebra.TensorProduct.assoc_aux_2
@[simp] theorem assoc_toLinearEquiv :
  (Algebra.TensorProduct.assoc R A B C).toLinearEquiv = _root_.TensorProduct.assoc R A B C := rfl
variable {A B C}
@[simp]
theorem assoc_tmul (a : A) (b : B) (c : C) :
    Algebra.TensorProduct.assoc R A B C ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl
@[simp]
theorem assoc_symm_tmul (a : A) (b : B) (c : C) :
    (Algebra.TensorProduct.assoc R A B C).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c :=
  rfl
end
variable {R S A}
def map (f : A →ₐ[S] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[S] B ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])
@[simp]
theorem map_tmul (f : A →ₐ[S] B) (g : C →ₐ[R] D) (a : A) (c : C) : map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
  rfl
@[simp]
theorem map_id : map (.id S A) (.id R C) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
theorem map_comp [Algebra S C] [IsScalarTower R S C]
    (f₂ : B →ₐ[S] C) (f₁ : A →ₐ[S] B) (g₂ : E →ₐ[R] F) (g₁ : D →ₐ[R] E) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
lemma map_id_comp (g₂ : E →ₐ[R] F) (g₁ : D →ₐ[R] E) :
    map (AlgHom.id S A) (g₂.comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
lemma map_comp_id [Algebra S C] [IsScalarTower R S C]
    (f₂ : B →ₐ[S] C) (f₁ : A →ₐ[S] B) :
    map (f₂.comp f₁) (AlgHom.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E)) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
@[simp]
theorem map_comp_includeLeft (f : A →ₐ[S] B) (g : C →ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by simp
@[simp]
theorem map_restrictScalars_comp_includeRight (f : A →ₐ[S] B) (g : C →ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by simp
@[simp]
theorem map_comp_includeRight (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g
theorem map_range (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← mul_one (f a), ← one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)
def congr (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[S] B ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)
@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl
@[simp]
theorem congr_apply (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A →ₐ[S] B) (g : C →ₐ[R] D)) x :=
  rfl
@[simp]
theorem congr_symm_apply (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : B →ₐ[S] A) (g.symm : D →ₐ[R] C)) x :=
  rfl
@[simp]
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : C ≃ₐ[R] C) = .refl :=
  AlgEquiv.coe_algHom_injective <| map_id
theorem congr_trans [Algebra S C] [IsScalarTower R S C]
    (f₁ : A ≃ₐ[S] B) (f₂ : B ≃ₐ[S] C) (g₁ : D ≃ₐ[R] E) (g₂ : E ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  AlgEquiv.coe_algHom_injective <| map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom
theorem congr_symm (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl
variable (R A B C) in
def leftComm : A ⊗[R] B ⊗[R] C ≃ₐ[R] B ⊗[R] A ⊗[R] C :=
  let e₁ := (Algebra.TensorProduct.assoc R A B C).symm
  let e₂ := congr (Algebra.TensorProduct.comm R A B) (1 : C ≃ₐ[R] C)
  let e₃ := Algebra.TensorProduct.assoc R B A C
  e₁.trans (e₂.trans e₃)
@[simp]
theorem leftComm_tmul (m : A) (n : B) (p : C) :
    leftComm R A B C (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl
@[simp]
theorem leftComm_symm_tmul (m : A) (n : B) (p : C) :
    (leftComm R A B C).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl
@[simp]
theorem leftComm_toLinearEquiv :
    (leftComm R A B C : _ ≃ₗ[R] _) = _root_.TensorProduct.leftComm R A B C := rfl
variable (R A B C D) in
def tensorTensorTensorComm : (A ⊗[R] B) ⊗[R] C ⊗[R] D ≃ₐ[R] (A ⊗[R] C) ⊗[R] B ⊗[R] D :=
  let e₁ := Algebra.TensorProduct.assoc R A B (C ⊗[R] D)
  let e₂ := congr (1 : A ≃ₐ[R] A) (leftComm R B C D)
  let e₃ := (Algebra.TensorProduct.assoc R A C (B ⊗[R] D)).symm
  e₁.trans (e₂.trans e₃)
@[simp]
theorem tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) :
    tensorTensorTensorComm R A B C D (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl
@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R A B C D).symm = tensorTensorTensorComm R A C B D := by
  ext; rfl
@[simp]
theorem tensorTensorTensorComm_toLinearEquiv :
    (tensorTensorTensorComm R A B C D : _ ≃ₗ[R] _) =
      _root_.TensorProduct.tensorTensorTensorComm R A B C D := rfl
end
end Monoidal
section
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
abbrev productLeftAlgHom (f : A →ₐ[S] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)
end
section
variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)
variable (R)
def lmul'' : S ⊗[R] S →ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x ↦ x.induction_on (by simp)
        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy ↦ by simp_all [hx, hy, mul_add] }
    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp
def lmul' : S ⊗[R] S →ₐ[R] S := (lmul'' R).restrictScalars R
variable {R}
theorem lmul'_toLinearMap : (lmul' R : _ →ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl
@[simp]
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=
  rfl
@[simp]
theorem lmul'_comp_includeLeft : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext <| mul_one
@[simp]
theorem lmul'_comp_includeRight : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext <| one_mul
variable (R S) in
def lmulEquiv [CompatibleSMul R S S S] : S ⊗[R] S ≃ₐ[S] S :=
  .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft <| AlgHom.ext fun x ↦ x.induction_on
    (by simp) (fun x y ↦ show (x * y) ⊗ₜ[R] 1 = x ⊗ₜ[R] y by
      rw [mul_comm, ← smul_eq_mul, smul_tmul, smul_eq_mul, mul_one])
    fun _ _ hx hy ↦ by simp_all [hx, hy, add_tmul]
def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g
theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl
@[simp]
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl
theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp
@[simp]
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp
@[simp]
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp,
    ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]
end
end TensorProduct
end Algebra
namespace LinearMap
open Algebra.TensorProduct
variable {R M₁ M₂ ι ι₂ : Type*} (A : Type*)
  [Fintype ι] [Finite ι₂] [DecidableEq ι]
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
end LinearMap
lemma Algebra.baseChange_lmul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {A : Type*} [CommRing A] [Algebra R A] (f : B) :
    (Algebra.lmul R B f).baseChange A = Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ f) := by
  ext i
  simp
namespace LinearMap
variable (R A M N : Type*) [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open Module
open scoped TensorProduct
@[simps!]
noncomputable
def tensorProduct : A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }
@[simps!]
noncomputable
def tensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, one_apply, one_eq_id, lTensor_id,
        LinearMap.id_apply])
end LinearMap
namespace Module
variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]
def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)
theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl
end Module
namespace TensorProduct.Algebra
variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]
def moduleAux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B →ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }
theorem moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a ⊗ₜ[R] b) m = a • b • m :=
  rfl
variable [SMulCommClass A B M]
protected def module : Module (A ⊗[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, LinearMap.map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw, smul_add]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [LinearMap.map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, LinearMap.map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]
attribute [local instance] TensorProduct.Algebra.module
theorem smul_def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl
end TensorProduct.Algebra