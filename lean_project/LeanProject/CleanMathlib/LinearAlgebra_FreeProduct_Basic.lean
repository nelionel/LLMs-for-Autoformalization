import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
universe u v w w'
namespace DirectSum
open scoped DirectSum
theorem induction_lon {R : Type*} [Semiring R] {ι: Type*} [DecidableEq ι]
    {M : ι → Type*} [(i: ι) → AddCommMonoid <| M i] [(i : ι) → Module R (M i)]
    {C: (⨁ i, M i) → Prop} (x : ⨁ i, M i)
    (H_zero : C 0)
    (H_basic : ∀ i (x : M i), C (lof R ι M i x))
    (H_plus : ∀ (x y : ⨁ i, M i), C x → C y → C (x + y)) : C x := by
  induction x using DirectSum.induction_on with
  | H_zero => exact H_zero
  | H_basic => exact H_basic _ _
  | H_plus x y hx hy => exact H_plus x y hx hy
end DirectSum
namespace RingQuot
universe uS uA uB
def algEquiv_quot_algEquiv
    {R : Type u} [CommSemiring R] {A B : Type v} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) (rel : A → A → Prop) :
    RingQuot rel ≃ₐ[R] RingQuot (rel on f.symm) :=
  AlgEquiv.ofAlgHom
    (RingQuot.liftAlgHom R (s := rel)
      ⟨AlgHom.comp (RingQuot.mkAlgHom R (rel on f.symm)) f,
      fun x y h_rel ↦ by
        apply RingQuot.mkAlgHom_rel
        simpa [Function.onFun]⟩)
    ((RingQuot.liftAlgHom R (s := rel on f.symm)
      ⟨AlgHom.comp (RingQuot.mkAlgHom R rel) f.symm,
      fun x y h ↦ by apply RingQuot.mkAlgHom_rel; simpa⟩))
    (by ext b; simp) (by ext a; simp)
def equiv_quot_equiv {A B : Type v} [Semiring A] [Semiring B] (f : A ≃+* B) (rel : A → A → Prop)  :
    RingQuot rel ≃+* RingQuot (rel on f.symm) :=
  let f_alg : A ≃ₐ[ℕ] B :=
    AlgEquiv.ofRingEquiv (f := f) (fun n ↦ by simp)
  algEquiv_quot_algEquiv f_alg rel |>.toRingEquiv
end RingQuot
open TensorAlgebra DirectSum TensorPower
variable {I : Type u} [DecidableEq I] {i : I} 
  (R : Type v) [CommSemiring R] 
  (A : I → Type w) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] 
  {B : Type w'} [Semiring B] [Algebra R B] 
  (maps : {i : I} → A i →ₐ[R] B) 
namespace LinearAlgebra.FreeProduct
instance : Module R (⨁ i, A i) := by infer_instance
abbrev FreeTensorAlgebra := TensorAlgebra R (⨁ i, A i)
abbrev PowerAlgebra := ⨁ (n : ℕ), TensorPower R n (⨁ i, A i)
@[reducible] noncomputable def powerAlgebra_equiv_freeAlgebra :
    PowerAlgebra R A ≃ₐ[R] FreeTensorAlgebra R A :=
  TensorAlgebra.equivDirectSum.symm
inductive rel : FreeTensorAlgebra R A → FreeTensorAlgebra R A → Prop
  | id  : ∀ {i : I}, rel (ι R <| lof R I A i 1) 1
  | prod : ∀ {i : I} {a₁ a₂ : A i},
      rel
        (tprod R (⨁ i, A i) 2 (fun | 0 => lof R I A i a₁ | 1 => lof R I A i a₂))
        (ι R <| lof R I A i (a₁ * a₂))
@[reducible, simp] def rel' := rel R A on ofDirectSum
theorem rel_id (i : I) : rel R A (ι R <| lof R I A i 1) 1 := rel.id
@[reducible] def _root_.LinearAlgebra.FreeProduct := RingQuot <| FreeProduct.rel R A
@[reducible] def _root_.LinearAlgebra.FreeProduct_ofPowers := RingQuot <| FreeProduct.rel' R A
noncomputable def equivPowerAlgebra : FreeProduct_ofPowers R A ≃ₐ[R] FreeProduct R A :=
  RingQuot.algEquiv_quot_algEquiv
    (FreeProduct.powerAlgebra_equiv_freeAlgebra R A |>.symm) (FreeProduct.rel R A)
  |>.symm
open RingQuot Function
local infixr:60 " ∘ₐ " => AlgHom.comp
instance instSemiring : Semiring (FreeProduct R A) := by infer_instance
instance instAlgebra : Algebra R (FreeProduct R A) := by infer_instance
abbrev mkAlgHom : FreeTensorAlgebra R A →ₐ[R] FreeProduct R A :=
  RingQuot.mkAlgHom R (rel R A)
abbrev ι' : (⨁ i, A i) →ₗ[R] FreeProduct R A :=
  (mkAlgHom R A).toLinearMap ∘ₗ TensorAlgebra.ι R (M := ⨁ i, A i)
@[simp] theorem ι_apply (x : ⨁ i, A i) :
  ⟨Quot.mk (Rel <| rel R A) (TensorAlgebra.ι R x)⟩ = ι' R A x := by
    aesop (add simp [ι', mkAlgHom, RingQuot.mkAlgHom, mkRingHom])
theorem identify_one (i : I) : ι' R A (DirectSum.lof R I A i 1) = 1 := by
  suffices ι' R A (DirectSum.lof R I A i 1) = mkAlgHom R A 1 by simpa
  exact RingQuot.mkAlgHom_rel R <| rel_id R A (i := i)
theorem mul_injections (a₁ a₂ : A i) :
    ι' R A (DirectSum.lof R I A i a₁) * ι' R A (DirectSum.lof R I A i a₂)
      = ι' R A (DirectSum.lof R I A i (a₁ * a₂)) := by
  convert RingQuot.mkAlgHom_rel R <| rel.prod
  aesop
abbrev lof (i : I) : A i →ₗ[R] FreeProduct R A :=
  ι' R A ∘ₗ DirectSum.lof R I A i
theorem lof_map_one (i : I) : lof R A i 1 = 1 := by
  rw [lof]; dsimp [mkAlgHom]; exact identify_one R A i
irreducible_def ι (i : I) : A i →ₐ[R] FreeProduct R A :=
  AlgHom.ofLinearMap (ι' R A ∘ₗ DirectSum.lof R I A i)
    (lof_map_one R A i) (mul_injections R A · · |>.symm)
irreducible_def of {i : I} : A i →ₐ[R] FreeProduct R A := ι R A i
@[simps] def lift : ({i : I} → A i →ₐ[R] B) ≃ (FreeProduct R A →ₐ[R] B) where
  toFun maps :=
    RingQuot.liftAlgHom R ⟨
        TensorAlgebra.lift R <|
          DirectSum.toModule R I B <|
            (@maps · |>.toLinearMap),
        fun x y r ↦ by
          cases r with
          | id => simp
          | prod => simp⟩
  invFun π i := π ∘ₐ ι R A i
  left_inv π := by
    ext i aᵢ
    aesop (add simp [ι, ι'])
  right_inv maps := by
    ext i a
    aesop (add simp [ι, ι'])
theorem lift_comp_ι : (lift R A maps) ∘ₐ (ι R A i) = maps := by
  ext a
  simp [lift_apply, ι]
@[aesop safe destruct] theorem lift_unique
    (f : FreeProduct R A →ₐ[R] B) (h : ∀ i, f ∘ₐ ι R A i = maps) :
    f = lift R A maps := by
  ext i a; simp_rw [AlgHom.ext_iff] at h; specialize h i a
  simp [h.symm, ι]
end LinearAlgebra.FreeProduct