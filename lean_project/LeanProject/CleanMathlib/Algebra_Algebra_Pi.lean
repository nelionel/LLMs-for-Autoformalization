import Mathlib.Algebra.Algebra.Equiv
universe u v w
namespace Pi
variable {I : Type u}
variable {R : Type*}
variable {f : I → Type v}
variable (x y : ∀ i, f i) (i : I)
variable (I f)
instance algebra {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] :
    Algebra R (∀ i : I, f i) :=
  { (Pi.ringHom fun i => algebraMap R (f i) : R →+* ∀ i : I, f i) with
    commutes' := fun a f => by ext; simp [Algebra.commutes]
    smul_def' := fun a f => by ext; simp [Algebra.smul_def] }
theorem algebraMap_def {_ : CommSemiring R} [_s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) : algebraMap R (∀ i, f i) a = fun i => algebraMap R (f i) a :=
  rfl
@[simp]
theorem algebraMap_apply {_ : CommSemiring R} [_s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    (a : R) (i : I) : algebraMap R (∀ i, f i) a i = algebraMap R (f i) a :=
  rfl
variable {I} (R)
@[simps!]
def algHom [CommSemiring R] [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    {A : Type*} [Semiring A] [Algebra R A] (g : ∀ i, A →ₐ[R] f i) :
      A →ₐ[R] ∀ i, f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp
@[simps]
def evalAlgHom {_ : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }
variable (A B : Type*) [CommSemiring R] [Semiring B] [Algebra R B]
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }
@[simp]
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl
@[simp]
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl
end Pi
instance Function.algebra {R : Type*} (I : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (I → A) :=
  Pi.algebra _ _
namespace AlgHom
variable {R : Type u} {A : Type v} {B : Type w} {I : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]
@[simps]
protected def compLeft (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }
end AlgHom
namespace AlgEquiv
@[simps apply]
def piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R] [∀ i, Semiring (A₁ i)]
    [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }
@[simp]
theorem piCongrRight_refl {R ι : Type*} {A : ι → Type*} [CommSemiring R] [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    (piCongrRight fun i => (AlgEquiv.refl : A i ≃ₐ[R] A i)) = AlgEquiv.refl :=
  rfl
@[simp]
theorem piCongrRight_symm {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
@[simp]
theorem piCongrRight_trans {R ι : Type*} {A₁ A₂ A₃ : ι → Type*} [CommSemiring R]
    [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)] [∀ i, Algebra R (A₁ i)]
    [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)] (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i)
    (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i => (e₁ i).trans (e₂ i) :=
  rfl
end AlgEquiv