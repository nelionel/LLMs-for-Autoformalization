import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
suppress_compilation
namespace MultilinearMap
section DomCoprod
open TensorProduct
variable {R ι₁ ι₂ ι₃ ι₄ : Type*}
variable [CommSemiring R]
variable {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁]
variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]
variable {N : Type*} [AddCommMonoid N] [Module R N]
@[simps apply]
def domCoprod (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) :
    MultilinearMap R (fun _ : ι₁ ⊕ ι₂ => N) (N₁ ⊗[R] N₂) where
  toFun v := (a fun i => v (Sum.inl i)) ⊗ₜ b fun i => v (Sum.inr i)
  map_update_add' _ i p q := by
    letI := (@Sum.inl_injective ι₁ ι₂).decidableEq
    letI := (@Sum.inr_injective ι₁ ι₂).decidableEq
    cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
  map_update_smul' _ i c p := by
    letI := (@Sum.inl_injective ι₁ ι₂).decidableEq
    letI := (@Sum.inr_injective ι₁ ι₂).decidableEq
    cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
def domCoprod' :
    MultilinearMap R (fun _ : ι₁ => N) N₁ ⊗[R] MultilinearMap R (fun _ : ι₂ => N) N₂ →ₗ[R]
      MultilinearMap R (fun _ : ι₁ ⊕ ι₂ => N) (N₁ ⊗[R] N₂) :=
  TensorProduct.lift <|
    LinearMap.mk₂ R domCoprod
      (fun m₁ m₂ n => by
        ext
        simp only [domCoprod_apply, TensorProduct.add_tmul, add_apply])
      (fun c m n => by
        ext
        simp only [domCoprod_apply, TensorProduct.smul_tmul', smul_apply])
      (fun m n₁ n₂ => by
        ext
        simp only [domCoprod_apply, TensorProduct.tmul_add, add_apply])
      fun c m n => by
      ext
      simp only [domCoprod_apply, TensorProduct.tmul_smul, smul_apply]
@[simp]
theorem domCoprod'_apply (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) : domCoprod' (a ⊗ₜ[R] b) = domCoprod a b :=
  rfl
theorem domCoprod_domDomCongr_sumCongr (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) :
    (a.domCoprod b).domDomCongr (σa.sumCongr σb) =
      (a.domDomCongr σa).domCoprod (b.domDomCongr σb) :=
  rfl
end DomCoprod
end MultilinearMap